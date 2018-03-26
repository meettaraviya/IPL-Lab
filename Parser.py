######################################################################################################
# 150050002 - 150050010
######################################################################################################

import sys

if len(sys.argv) < 2:
	print('Usage : python parser.py <filename>')
	exit(0)

file = open(sys.argv[1], 'r')
program = file.read()
file.close()
astfile = open(sys.argv[1] + ".ast", 'w')
cfgfile = open(sys.argv[1] + ".cfg", 'w')

if astfile is None:
	print("Could not open file")
	exit(1)

from Lexer import *

######################################################################################################
# PARSER
######################################################################################################

import ply.yacc as yacc

operator = {
		"PLUS":"+",
		"MINUS":"-",
		"MUL":"*",
		"DIV":"/",
		"LT":"<",
		"GT":">",
		"LE":"<=",
		"GE":">=",
		"EQ":"==",
		"NE":"!=",
		"AND":"&&",
		"OR":"||",
	}

class Scope:

	def __init__(self, parent=None):
		self.symbols = dict()
		self.parent = parent

class Type:

	def __init__(self, name, indirection, type, width, offset):
		self.name = name
		self.indirection = indirection
		self.type = type
		self.width = width
		self.offset = offset

	def setFunctionProperties(self, scope, params, return_type, is_proto=None):
		self.scope = scope
		self.params = params
		self.return_type = return_type
		self.is_proto = is_proto

global_symbols = Scope()
current_ST_node = global_symbols

class CFG_Node:
	block_id, t_id = 0, 0
	block_code = dict()
	block_goto = [None]
	def __init__(self, astNode, new_block = False, parent=''):

		self.children = []

		child_new_block = new_block

		if new_block and (astNode.name=='ASGN' or (parent=='IF' or parent=='WHILE')):
			CFG_Node.block_id += 1
			CFG_Node.block_goto.append(None)
			CFG_Node.block_code[CFG_Node.block_id] = []

		self.block = CFG_Node.block_id

		child_parent = astNode.name

		for child in astNode.children:
			child_cfg = CFG_Node(child, child_new_block or astNode.name=="IF" or astNode.name=="WHILE", child_parent)
			child_parent = ''
			self.children.append(child_cfg)
			child_new_block = child.name=="IF" or child.name=="WHILE"

		if astNode.name == "ASGN":
			self.code = self.children[1].code + [(self.children[0].address,"=", self.children[1].address)]
			CFG_Node.block_code[self.block] += self.code

		elif astNode.name in operator:
			self.address = 't' + str(CFG_Node.t_id)
			CFG_Node.t_id += 1
			self.code = self.children[0].code + self.children[1].code + [(self.address, '=', self.children[0].address, operator[astNode.name], self.children[1].address)]
	
		elif astNode.name == "UMINUS":
			self.address = 't' + str(CFG_Node.t_id)
			CFG_Node.t_id += 1
			self.code = self.children[0].code + [(self.address, '=', '-', self.children[0].address)]

		elif astNode.name == "DEREF":
			self.address = '*' + self.children[0].address
			self.code = []
	
		elif astNode.name == "ADDR":
			self.address = '&' + self.children[0].address
			self.code = []
	
		elif astNode.name == "VAR" or astNode.name == "CONST":
			self.address = str(astNode.value)
			self.code = []
	
		elif astNode.name == "IF":
			self.code = []
			self.address = self.children[0].address
			self.block = self.children[0].block
			CFG_Node.block_code[self.children[0].block] = self.children[0].code
	
		elif astNode.name == "WHILE":
			self.code = []
			self.address = self.children[0].address
			self.block = self.children[0].block
			CFG_Node.block_code[self.children[0].block] = self.children[0].code
	
		elif astNode.name == "STMLIST":
			self.code = []
			if len(self.children)>0:
				self.block = self.children[0].block
			for child in self.children:
				self.code += child.code

		else:
			print (astNode.name)
			raise Exception

	def buildGraph(self, astNode, nextBlock = -1):
		
		if nextBlock==-1:
			nextBlock = len(CFG_Node.block_code)+1

		if astNode.name=='IF':

			if len(self.children)==3:
				ifTarget = self.children[1].block
				elseTarget = self.children[2].block
				if len(self.children[1].children)==0:
					ifTarget = nextBlock
				if len(self.children[2].children)==0:
					elseTarget = nextBlock
				CFG_Node.block_goto[self.children[0].block] = (ifTarget, elseTarget, True, self.address)
				self.children[1].buildGraph(astNode.children[1], nextBlock)
				self.children[2].buildGraph(astNode.children[2], nextBlock)
			elif len(self.children)==2:
				ifTarget = self.children[1].block
				if len(self.children[1].children)==0:
					ifTarget = nextBlock
				CFG_Node.block_goto[self.children[0].block] = (ifTarget, nextBlock, True, self.address)
				self.children[1].buildGraph(astNode.children[1], nextBlock)


		elif astNode.name=='WHILE':

			if len(self.children)==2:
				CFG_Node.block_goto[self.children[0].block] = (self.children[1].block, nextBlock, True, self.address)
				self.children[1].buildGraph(astNode.children[1], self.children[0].block)
			else:
				CFG_Node.block_goto[self.children[0].block] = (self.children[0].block, nextBlock, True, self.address)

		elif astNode.name=='STMLIST':

			for i in range(len(self.children)):
				if i<len(self.children)-1:
					self.children[i].buildGraph(astNode.children[i], self.children[i+1].block)
				else:
					self.children[i].buildGraph(astNode.children[i], nextBlock)

		else:

			CFG_Node.block_goto[self.block] = (nextBlock, nextBlock, False)


	def __str__(self):
		cfg_str = ''
		for block,code in CFG_Node.block_code.items():
			cfg_str += "<bb " + str(block) + ">\n"
			for line in code:
				cfg_str += ' '.join([str(word) for word in line])+'\n'
			t = CFG_Node.block_goto[block]
			if t[2]:
				cfg_str += 'if(%s) goto <bb %d>\nelse goto <bb %d>\n'%(t[3], t[0], t[1])
			else:
				cfg_str += 'goto <bb %d>\n'%(t[0],)
			cfg_str += '\n'
		cfg_str += '<bb %d>\nEnd\n'%(CFG_Node.block_id+1,)
		return cfg_str
	
class AST_Node:
	def __init__(self,name,children=None, value=None):
		
		self.name = name
		self.value = value
		
		if children is not None:
			self.children = children
			self.leaf = False
			# self.has_var = False
			# for child in children:
				# self.has_var = self.has_var or child.has_var
		
		else:
			# if self.name=="CONST":
			# 	self.has_var = False
			# else:
			# 	self.has_var = True
			self.children = []
			self.leaf = True
	
	def __str__(self):
		
		if self.leaf:
			return '\n' + self.name+'('+str(self.value)+')'
		
		else:
			ast_str = '\n' + self.name + '\n('
			sep = '\n,'
			rep = '\n\t'
			if self.name=='STMLIST':
				ast_str = ''
				sep = ''
				rep = '\n'
			ast_str += sep.join([str(child) for child in self.children]).replace('\n', rep)
			if self.name!='STMLIST':
				ast_str += '\n)'
			return ast_str

	__repr__ = __str__


precedence = (
		('left', 'LOR'),
		('left', 'LAND'),
		('left', 'EE', 'NE'),
		('left', 'LT', 'GT', 'LTE', 'GTE'),
		('left', 'PLUS', 'MINUS'),
        ('left', 'ASTERISK', 'FSLASH'),
        ('right', 'UMINUS'),
        ('right', 'DEREF'),
		('right', 'IF_BLOCK', 'ELSE'),
)

def p_program(p):
	"""program : declaration_list function_list"""
	print("Successfully Parsed")

def p_declaration_list(p):
	"""declaration_list : declaration_list declaration SEMICOLON
		| empty"""

def p_function_list(p):
	"""function_list : function
		| function function_list"""

def p_function(p):
	"""function : VOID IDENTIFIER LPAREN paramlist RPAREN function_dummy LBRACE function_body RBRACE
		| DATA_TYPE IDENTIFIER LPAREN paramlist RPAREN function_dummy LBRACE function_body RBRACE
		| DATA_TYPE IDENTIFIER LPAREN paramlist RPAREN function_proto_dummy SEMICOLON
		| VOID IDENTIFIER LPAREN paramlist RPAREN function_proto_dummy SEMICOLON"""
	global current_ST_node
	current_ST_node = current_ST_node.parent



def p_paramlist(p):
	"""paramlist : DATA_TYPE decl_var 
		| paramlist COMMA DATA_TYPE decl_var
		| empty"""
	if len(p)==2:
		p[0] = []
	elif len(p)==3:
		p[0] = [(p[1], p[2][1], p[2][0])]
	else:
		p[0] = p[1] + [(p[3], p[4][1], p[4][0])]



def p_function_body(p):
	"""function_body : statement_list"""
	astfile.write(str(p[1]))
	
	# cfg = CFG_Node(p[1], new_block = True)
	# cfg.buildGraph(p[1])
	# cfgfile.write(str(cfg))

	p[0] = p[1]

def p_function_dummy(p):
	"""function_dummy : empty"""
	global current_ST_node
	if p[-4] in current_ST_node.symbols and not current_ST_node.symbols[p[-4]].is_proto:
		print('Declared again: %s'%(p[-4],))
		exit(1)
	else:
		if p[-4] in current_ST_node.symbols:
			known_params = current_ST_node.symbols[p[-4]].params
			known_return_type = current_ST_node.symbols[p[-4]].return_type

			if known_return_type!=p[-5]:
				print('Return type not matching: %s'%(p[-4],))
				exit(1)
			else:
				params_same = True
				if len(known_params)!=len(p[-2]):
					params_same = False
				i = 0
				while i<len(known_params) and i<len(p[-2]) and params_same:
					if known_params[i][0]!=p[-2][i][0] or known_params[i][1]!=p[-2][i][1]:
						params_same = False
					i += 1
				if not params_same:
					print('Function prototype not followed: %s'%(p[-4],))
					exit(1)
		scope = Scope(parent=current_ST_node)
		for param in p[-2]:
			param_type = Type(param[2], param[1], param[0], 0, 0)
			scope.symbols[param[2]] = param_type
		type = Type(p[-4], None, 'FUNCTION', None, 0)
		type.setFunctionProperties(scope, p[-2], p[-5], is_proto=False)
		current_ST_node.symbols[p[-4]] = type
		current_ST_node = scope


def p_function_proto_dummy(p):
	"""function_proto_dummy : empty"""
	global current_ST_node
	if p[-4] in current_ST_node.symbols:
		print('Declared again: %s'%(p[-4],))
		exit(1)
	else:
		scope = Scope(parent=current_ST_node)
		type = Type(p[-4], None, 'FUNCTION', None, 0)
		type.setFunctionProperties(scope, p[-2], p[-5], is_proto=True)
		current_ST_node.symbols[p[-4]] = type
		current_ST_node = scope

def p_statement_list(p):
	"""statement_list : statement_list statement
		| empty"""
	if p[1]=='':
		p[0] = AST_Node("STMLIST", children=[])
	else:
		p[0] = AST_Node("STMLIST", children=p[1].children+p[2])

def p_statement(p):
	"""statement : declaration SEMICOLON
		| assignment SEMICOLON
		| RETURN expression SEMICOLON
		| while_block
		| if_else_block"""
	if p[1]=='return':
		p[0] = [AST_Node('RETURN', children=[p[2]])]
	elif p[1].name=='DECL':
		p[0] = []
	else:
		p[0] = [p[1]]

def p_statement_block(p):
	"""statement_block : statement
		| SEMICOLON
		| LBRACE statement_list RBRACE"""
	if p[1]==';':
		p[0] = AST_Node("STMLIST", children=[])
	elif p[1]=='{':
		p[0] = p[2]
	else:
		p[0] = AST_Node("STMLIST", children=p[1])


def p_if_block(p):
	"""if_block : IF LPAREN condition RPAREN statement_block"""
	p[0] = [p[3], p[5]]

def p_else_block(p):
	"""else_block : ELSE statement_block"""
	p[0] = [p[2]]

def p_if_else_block(p):
	"""if_else_block : if_block %prec IF_BLOCK
		| if_block else_block"""
	if len(p) == 2:
		p[0] = AST_Node('IF', children = p[1])
	else:
		p[0] = AST_Node('IF', children = p[1]+p[2])

def p_while_block(p):
	"""while_block : WHILE LPAREN condition RPAREN statement_block"""
	p[0] = AST_Node('WHILE', children = [p[3], p[5]])

def p_declaration(p):
	"""declaration : DATA_TYPE decl_var_list"""
	for var in p[2]:
		if var[0] in current_ST_node.symbols:
			print('Variable declared again %s'%(var[0],))
			exit(1)
		else:
			current_ST_node.symbols[var[0]] = Type(var[0], var[1], p[1], 0, 0)
	p[0] = AST_Node('DECL')

def p_decl_var_list(p):
	"""decl_var_list : decl_var 
		| decl_var_list COMMA decl_var"""
	if len(p)==2:
		p[0] = [p[1]]
	else:
		p[0] = p[1]+[p[3]]

def p_decl_var(p):
	"""decl_var : IDENTIFIER
		| ASTERISK decl_var %prec DEREF"""
	if p[1]=='*':
		p[0] = (p[2][0], p[2][1]+1)
	else:
		p[0] = (p[1], 0)
 
def p_pointer_var(p):
	"""pointer_var : ASTERISK pointer_var
		| ASTERISK scalar_var"""
	p[0] = AST_Node("DEREF", children = [p[2]])

def p_scalar_var(p):
	"""scalar_var : IDENTIFIER
		| AMPERSAND scalar_var
		| AMPERSAND pointer_var"""
	if p[1] == '&':
		p[0] = AST_Node("ADDR", children = [p[2]])
	else:
		p[0] = AST_Node("VAR", value = p[1])
		checked_node = current_ST_node
		while checked_node is not None and p[1] not in checked_node.symbols:
			checked_node = checked_node.parent
		if checked_node is None:
			print('Unknown symbol %s'%(p[1],))
			exit(1)

def p_assignment(p):
	"""assignment : pointer_var EQUALS expression
		| IDENTIFIER EQUALS expression"""
	if isinstance(p[1], str):
		p[1] = AST_Node("VAR", value=p[1])
		# if not p[3].has_var:
		# 	print("Syntax error at '=' line no  '%d' "%p.lexer.lineno)
		# 	exit(1)

	p[0] = AST_Node("ASGN", children = [p[1],p[3]])


def p_expression_add(p):
	"""expression : expression PLUS expression"""
	p[0] = AST_Node("PLUS", children = [p[1],p[3]])

def p_expression_subtract(p):
	"""expression : expression MINUS expression"""
	p[0] = AST_Node("MINUS", children = [p[1],p[3]])

def p_expression_parenthesis(p):
	"""expression : LPAREN expression RPAREN"""
	p[0] = p[2]

def p_expression_multiply(p):
	"""expression : expression ASTERISK expression"""
	p[0] = AST_Node("MUL", children = [p[1],p[3]])

def p_expression_divide(p):
	"""expression : expression FSLASH expression"""
	p[0] = AST_Node("DIV", children = [p[1],p[3]])

def p_expression_negation(p):
	"""expression : MINUS expression %prec UMINUS"""
	p[0] = AST_Node("UMINUS", children = [p[2]])

def p_expression_function_call(p):
	"""expression : IDENTIFIER LPAREN arglist RPAREN
		| IDENTIFIER LPAREN RPAREN"""
	if len(p)==5:
		p[0] = AST_Node("FCALL", children = [p[1], p[3]])
	else:
		p[0] = AST_Node("FCALL", children = [p[1], AST_Node("ARGLIST", children=[])])

def p_arglist(p):
	"""arglist : arglist COMMA expression
		| expression"""
	if len(p)==2:
		p[0] = AST_Node("ARGLIST", children=[p[1]])
	else:
		p[0] = AST_Node("ARGLIST", children=p[1].children + [p[3]])


def p_condition_ee(p):
	"""condition : expression EE expression"""
	p[0] = AST_Node("EQ", children = [p[1],p[3]])

def p_condition_ne(p):
	"""condition : expression NE expression"""
	p[0] = AST_Node("NE", children = [p[1],p[3]])

def p_condition_lt(p):
	"""condition : expression LT expression"""
	p[0] = AST_Node("LT", children = [p[1],p[3]])

def p_condition_gt(p):
	"""condition : expression GT expression"""
	p[0] = AST_Node("GT", children = [p[1],p[3]])

def p_condition_lte(p):
	"""condition : expression LTE expression"""
	p[0] = AST_Node("LE", children = [p[1],p[3]])

def p_condition_gte(p):
	"""condition : expression GTE expression"""
	p[0] = AST_Node("GE", children = [p[1],p[3]])

def p_condition_land(p):
	"""condition : condition AMPERSAND AMPERSAND condition %prec LAND"""
	p[0] = AST_Node("AND", children = [p[1], p[4]])

def p_condition_lor(p):
	"""condition : condition PIPE PIPE condition %prec LOR"""
	p[0] = AST_Node("OR", children = [p[1], p[4]])

def p_condition_parenthesis(p):
	"""condition : LPAREN condition RPAREN"""
	p[0] = p[2]

def p_expression_base_constant(p):
	"""expression : CONSTANT"""
	p[0] = AST_Node("CONST", value = p[1])

def p_expression_base_var(p):
	"""expression : pointer_var
		| scalar_var"""
	p[0] = p[1]

def p_error(p):
	print("Syntax error at '%s' line no  '%d' " % (p.value, p.lexer.lineno,))
	exit(1)

def p_empty(p):
	"""empty :"""
	p[0] = ''


yacc.yacc()
yacc.parse(program, debug=False)
astfile.close()
cfgfile.close()
