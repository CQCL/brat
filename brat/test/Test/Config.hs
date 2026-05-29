module Test.Config (ValidationConfig(..)) where

import Data.Tagged (Tagged(..))
import Test.Tasty.Options (IsOption(..), flagCLParser)

data ValidationConfig = IgnoreValidation | RunValidation

instance IsOption ValidationConfig where
  defaultValue = RunValidation
  parseValue s = if s == "ignore-validation" then Just RunValidation else Nothing
  optionName = Tagged "ignore-validation"
  optionHelp = Tagged "Don't mark validation failures as failures"
  optionCLParser = flagCLParser Nothing IgnoreValidation
