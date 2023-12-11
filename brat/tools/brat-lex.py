from pygments.lexer import RegexLexer, bygroups
from pygments.token import *

class CustomLexer(RegexLexer):
    name = 'brat'
    aliases = ['brat','Brat','BRAT']
    filenames = ['*.brat']

    tokens = {
        'root': [
            (r'--.*\n', Comment),
            (r'->', Operator),
            (r'=>', Operator),
            (r'-o', Operator),
            (r'=', Operator),
            (r'==', Operator),
            (r'(::)( *)(\*)', bygroups(Operator, Whitespace, Keyword.Type)),
            (r'[;:,\|>]', Operator),
#            (r'([a-z][a-zA-Z-_0-9\']*)\((.*)\) *[:-[>o])', bygroups(Name, 'root', Operator)),
            (r'([^a-z])(cons)', bygroups(Text, Keyword.Pseudo)),
            (r'^cons', Keyword.Pseudo),
            (r'nil', Keyword.Pseudo),
            (r'zero', Keyword.Pseudo),
            (r'succ', Keyword.Pseudo),
            (r'doub', Keyword.Pseudo),
            (r'some', Keyword.Pseudo),
            (r'none', Keyword.Pseudo),
            (r'true', Keyword.Pseudo),
            (r'false', Keyword.Pseudo),
            (r'^(import)( *)(qualified)?( *)([a-zA-Z0-9-_]*)( *)(as)?', bygroups(Keyword.Reserved, # import
                                                                                 Whitespace,       #
                                                                                 Keyword.Reserved, # qualified
                                                                                 Whitespace,       #
                                                                                 Text,             # <module>
                                                                                 Whitespace,       #
                                                                                 Keyword.Reserved  # as
                                                                                 )),
            (r'let', Keyword),
            (r'in', Keyword),
            (r'Int', Keyword.Type),
            (r'(in) ', Keyword),
            (r'\#', Keyword.Type),
            (r'Vec', Keyword.Type),
            (r'Fin', Keyword.Type),
            (r'List', Keyword.Type),
            (r'Bool', Keyword.Type),
            (r'Nat', Keyword.Type),
            (r'Qubit', Keyword.Type),
            (r'Bit', Keyword.Type),
            (r'Option', Keyword.Type),
            (r'Float', Keyword.Type),
            (r'Money', Keyword.Type),
            (r'^([a-zA-Z0-9\']*)( *)(\()', bygroups(Name.Function,Whitespace, Text), 'root'),
            (r'^([a-zA-Z0-9\']*)( *)(=)( *)', bygroups(Name.Function,Whitespace,Text,Whitespace)),
#            (r'[-;,=#\*]', Operator),
#            (r'\+.*\n', Generic.Inserted),
#            (r'-.*\n', Generic.Deleted),
#            (r'@.*\n', Generic.Subheading),
#            (r'Index.*\n', Generic.Heading),
#            (r'=.*\n', Generic.Heading),
            (r'([ \(\[\{,])(-?[0-9]+\.?[0-9]*)', bygroups(Text, Number)),
#            (r'".*"', String),
            (r'.', Text)
        ]
    }
