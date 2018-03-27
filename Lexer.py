######################################################################################################
# LEXER
######################################################################################################

import ply.lex as lex

tokens = (
	'DATA_TYPE',
	'IDENTIFIER',
	'CONSTANT',

	'EQUALS',
	'SEMICOLON',
	'ASTERISK',
	'AMPERSAND',
	'COMMA',
	'FSLASH',
	'PLUS',
	'MINUS',

	'LT',
	'GT',
	'LTE',
	'GTE',
	'EE',
	'NE',
	# 'BAND',
	'PIPE',

	'IF',
	'ELSE',
	'WHILE',

	'LPAREN',
	'RPAREN',
	'LBRACE',
	'RBRACE',

	'NEWLINE',
	'VOID',
	'RETURN',
	)

keywords = {
   'if' : 'IF',
   'then' : 'THEN',
   'else' : 'ELSE',
   'while' : 'WHILE',
   'int' : 'DATA_TYPE',
   'float' : 'DATA_TYPE',
   'void': 'VOID',
   'return' : 'RETURN',
}

def t_error(t):
	print("Illegal character %s" % (t.value[0],) )
	t.lexer.skip(1)

# def t_MAIN(t):
# 	r'main'
# 	return t

t_ignore = ' \t'

def t_NEWLINE(t):
	r'(\r?\n)+'
	t.lexer.lineno += len(t.value)

# def t_DATA_TYPE(t):
# 	r'int|void'
# 	return t

# def t_IF(t):
# 	r'if'
# 	return t

# def t_ELSE(t):
# 	r'else'
# 	return t

# def t_WHILE(t):
# 	r'while'
# 	return t


# t_IDENTIFIER = r'[_a-zA-Z][_a-zA-Z0-9]{0,30}'

def t_IDENTIFIER(t):
	r'[a-zA-Z_][a-zA-Z_0-9]*'
	t.type = keywords.get(t.value,'IDENTIFIER')    # Check for reserved words
	return t



def t_CONSTANT(t):
	r'[0-9]+(\.[0-9]+)?'
	try:
		t.value = int(t.value)
	except ValueError:
		t.value = float(t.value)
	except ValueError:
		print('Illegal constant')
		t.value = 0
	return t

t_EQUALS = r'\='
t_SEMICOLON = r'\;'
t_ASTERISK = r'\*'
t_AMPERSAND = r'\&'
t_COMMA = r'\,'
t_LPAREN = r'\('
t_RPAREN = r'\)'
t_LBRACE = r'\{'
t_RBRACE = r'\}'
t_PLUS = r'\+'
t_MINUS = r'\-'
t_FSLASH = r'\/'
t_LT = r'<'
t_GT = r'>'
t_LTE = r'<='
t_GTE = r'>='
t_EE = r'=='
t_NE = r'!='
# t_BAND = r'&'
t_PIPE = r'\|'

lexer = lex.lex()

