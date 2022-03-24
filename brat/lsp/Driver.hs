{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

import Control.Concurrent.MVar
import Control.Lens hiding (Iso)
import Control.Monad.Except
import Data.Maybe (fromMaybe)
import Data.Rope.UTF16 (toString)
import Data.Text (pack)
import Language.LSP.Server
import Language.LSP.Diagnostics
import Language.LSP.Types
import Language.LSP.Types.Lens hiding (publishDiagnostics, textDocumentSync)
import Language.LSP.VFS
import System.FilePath (dropFileName)
import System.Log.Logger

import Brat.Checker (TypedHole)
import Brat.Error
import Brat.FC as FC
import Brat.Load
import Brat.LSP.Find
import Brat.LSP.Holes
import Brat.LSP.State

main :: IO Int
main = do
  ps   <- newMVar emptyPS
  setupLogger Nothing ["lsp-brat"] DEBUG

  runServer $ ServerDefinition
      { defaultConfig = ()
      , onConfigurationChange = \old _ -> pure old
      , doInitialize = \env _ -> pure (Right env)
      , staticHandlers = handlers ps
      , interpretHandler = \env -> Iso (runLspT env) liftIO
      , options = defaultOptions { textDocumentSync = Just syncOptions }
      }
 where
  syncOptions :: TextDocumentSyncOptions
  syncOptions = TextDocumentSyncOptions
    { _openClose         = Just True
    , _change            = Just TdSyncIncremental
    , _willSave          = Just False
    , _willSaveWaitUntil = Just False
    , _save              = Just $ InR $ SaveOptions $ Just False
    }

sendError :: NormalizedUri -> Error -> LspM () ()
sendError fileUri Err{..} =
  let startPos = maybe (Position 0 0)   (conv . FC.start) fc
      endPos   = maybe (Position 0 100) (conv . FC.end) fc
      diags = [Diagnostic
               (Range startPos endPos)
               (Just DsError)
               Nothing
               (Just "lsp-brat")
               (pack $ show msg)
               Nothing
               Nothing
              ]
  in publishDiagnostics 1 fileUri Nothing (partitionBySource diags)
 where
  conv :: Pos -> Position
  conv p@(Pos l c) = case msg of
                        LexErr _ -> Position l c
                        _ -> convPos p

convPos :: Pos -> Position
convPos (Pos l c) = Position (max 0 (l - 1)) (max 0 (c - 1))

-- publish 0 error messages (to delete old ones)
allGood :: NormalizedUri -> LspM () ()
allGood fileUri = publishDiagnostics 0 fileUri Nothing (partitionBySource [])

logHoles :: [TypedHole] -> NormalizedUri -> LspM () ()
logHoles hs fileUri = publishDiagnostics (length hs) fileUri Nothing (partitionBySource (logHole <$> hs))
 where
  logHole :: TypedHole -> Diagnostic
  logHole h = let (FC start end, info) = holeInfo h
                  msg = pack info
                  range = Range (convPos start) (convPos end)
              in  Diagnostic
                  range
                  (Just DsInfo)
                  Nothing
                  (Just "lsp-brat")
                  msg
                  Nothing
                  Nothing

loadVFile state method msg = do
  let fileUri = msg ^. params
                . textDocument
                . uri
  let fileName = fileUri ^. to toNormalizedUri
  file <- getVirtualFile fileName
  let cwd = fromMaybe "" $ dropFileName <$> (uriToFilePath fileUri)
  case file of
    Just (VirtualFile _version str rope) -> do
      let file = toString rope
      liftIO $ debugM "loadVFile" $ "Found file: " ++ show str
      env <- liftIO . runExceptT $ loadFiles Lib cwd (show fileName) file
      case env of
        Right (_,newDecls,holes,_) -> do
          old@(PS oldDecls _ oldHoles) <- liftIO $ takeMVar state
          if (oldDecls, oldHoles) == (newDecls, holes)
            then liftIO (putMVar state old) >> allGood fileName
            else do
              liftIO $ debugM "loadVFile" $ "Updated ProgramState"
              liftIO $ putMVar state (updateState (newDecls, holes) old)
              allGood fileName
              logHoles holes fileName
        Left err -> allGood fileName *> sendError fileName (fixParseError err)
    Nothing -> do
      liftIO $ debugM "loadVFile" $ "Couldn't find " ++ show fileName ++ " in VFS"
 where
  fixParseError err@(Err _ _ (ParseErr _))
   = case fc err of
       Just (FC st nd) -> let conv (Pos l c) = Pos (l + 1) (c + 1)
                          in  err { fc = Just (FC (conv st) (conv nd)) }
       Nothing -> err
  fixParseError err = err

handlers :: MVar ProgramState -> Handlers (LspM ())
handlers state = mconcat
  [ notificationHandler SInitialized $ const (pure ())
  , notificationHandler STextDocumentDidOpen (loadVFile state "TextDocumentDidOpen")
  , notificationHandler STextDocumentDidChange (loadVFile state "TextDocumentDidChange")
  , notificationHandler STextDocumentDidSave (loadVFile state "TextDocumentDidSave")
  -- Do nothing, never cancel!
  , notificationHandler SCancelRequest (const (pure ()))
  -- TODO: on hover, give some info
  , requestHandler STextDocumentHover $ \req responder -> do
      let conv (Position l c) = Pos (l + 1) (c + 1)
      st <- liftIO $ readMVar state
      liftIO $ debugM "handlers" "TextDocumentHover"
      let HoverParams _ pos _ = req ^. params
          -- Dummy info to respond with
          info = pack . show <$> getInfo st (conv pos)
          ms = maybe mempty (HoverContents . unmarkedUpContent) info
          range = Range pos pos
          rsp = Hover ms (Just range)
      responder (Right $ Just rsp)
  ]
