import { workspace, ExtensionContext } from 'vscode';

import {
	LanguageClient,
	LanguageClientOptions,
	ServerOptions,
	ExecutableOptions,
	Executable
} from 'vscode-languageclient/node';

let client: LanguageClient;

export function activate(context: ExtensionContext) {
	const config = workspace.getConfiguration('brat');
	let serverCommand = config.get<string>('lspPath');
	let commandOptions: ExecutableOptions = { shell: true, detached: false };
	
	const serverOptions: ServerOptions = {
		run: <Executable>{ command: serverCommand, options: commandOptions },
		debug: <Executable>{ command: serverCommand, options: commandOptions },
	};

	const clientOptions: LanguageClientOptions = {
		documentSelector: [{ scheme: 'file', language: 'brat' }],
		synchronize: { }
	};

	client = new LanguageClient(
		'brat-lsp-client',  // Identifier, can be chosen arbitrarily
		'Brat LSP',         // Display name
		serverOptions,
		clientOptions
	);

	// Start the client. This will also launch the server
	client.start();
}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}
