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
symfile = open(sys.argv[1] + ".sym", 'w')

if astfile is None or cfgfile is None or symfile is None:
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


	def __init__(self, parent=None, function=None):
		self.symbols = dict()
		self.parent = parent
		self.function = function

	def __str__(self):
		string = ""
		string += "Procedure table :-\n"
		string += "-----------------------------------------------------------------\n"
		string += "Name\t\t|\tReturn Type  |  Parameter List\n"
		for symbol in sorted(self.symbols.keys()):
			variable = self.symbols[symbol]
			if variable.type == 'FUNCTION':
				string += '%s\t\t|\t%s'%(variable.name, variable.return_type)+'\t|\t%s\n'%(variable.getParams(),)
		string += "-----------------------------------------------------------------\n"
		string += "Variable table :- \n"
		string += "-----------------------------------------------------------------\n"
		string += "Name\t|\tScope\t\t|\tBase Type  |  Derived Type\n"
		string += "-----------------------------------------------------------------\n"
		for symbol in sorted(self.symbols.keys()):
			variable = self.symbols[symbol]
			if variable.type != 'FUNCTION':
				string += '%s\t\t|\tglobal\t\t|\t%s\t   |\t'%(variable.name, variable.type)+'*'*variable.indirection+'\n'
			else:
				string+='\n'
				function_ST = variable.scope
				for symbol,local_variable in function_ST.symbols.items():
					string += '%s\t\t|\tprocedure %s\t|\t%s\t   |\t'%(local_variable.name, variable.name, local_variable.type)+'*'*variable.indirection+'\n'
		string += "-----------------------------------------------------------------\n"
		string += "-----------------------------------------------------------------\n"
				
		return string


	def calculate_offsets(self):
		local_vars = []
		offset = 4
		print(self.function.name)
		for name in sorted(self.symbols.keys()):
			variable = self.symbols[name]
			print(name, variable.is_param)
			if not variable.is_param:
				variable.offset = offset
				offset += variable.width
		offset += 8 # for fp and ra

		for param in self.function.params:
			variable = self.symbols[param.name]
			variable.offset = offset
			offset += variable.width

		print(self.function.name)
		for name in sorted(self.symbols.keys()):
			print(name, self.symbols[name].offset)




class Type:

	def __init__(self, name, indirection, type, width, offset, is_param=False):
		self.name = name
		self.indirection = indirection
		self.type = type
		self.width = width
		self.offset = offset
		self.is_param = is_param

	def setFunctionProperties(self, scope, params, return_type, is_proto=None):
		self.scope = scope
		self.params = params
		self.return_type = return_type
		self.is_proto = is_proto

	def getParams(self):
		return ', '.join([param.type + ' ' + '*'*param.indirection + param.name for param in self.params])
		# return '{%s}'%(','.join(["'%s' : '%s'"%(k.name,str(k)) for k in self.params]),)

	def __str__(self):
		return self.type+'*'*self.indirection
		# return str(self.__dict__)

	__repr__ = __str__

global_symbols = Scope()
current_ST_node = global_symbols
block_id, t_id = -1, 0
block_code = dict()
block_goto = [None]
class CFG_Node:

	def __init__(self, astNode, new_block = False, parent=''):
		global block_id, t_id, block_code
		self.children = []

		child_new_block = new_block

		if new_block and (astNode.name=='ASGN' or astNode.name=='RETURN ' or (astNode.name=='FCALL' and astNode.is_statement) or (parent=='IF' or parent=='WHILE')):
			block_id += 1
			block_goto.append(None)
			block_code[block_id] = []

		self.block = block_id
		child_parent = astNode.name

		for child in astNode.children:
			child_cfg = CFG_Node(child, child_new_block or astNode.name=="IF" or astNode.name=="WHILE", child_parent)
			child_parent = ''
			self.children.append(child_cfg)
			child_new_block = child.name=="IF" or child.name=="WHILE"

		if astNode.name == "ASGN":
			self.code = self.children[1].code + [(self.children[0].address,"=", self.children[1].address)]
			block_code[self.block] += self.code
		
		elif astNode.name == "ARGLIST":
			self.code = []
			self.address = []
			for child in self.children:
				self.code += child.code
				self.address += [child.address]

		elif astNode.name == "FCALL" and not astNode.is_statement:
			self.address = astNode.value + "(" + ", ".join([str(param) for param in self.children[0].address]) + ")"
			self.code = self.children[0].code
		
		elif astNode.name == "FCALL" and astNode.is_statement:
			self.address = astNode.value + "(" + ", ".join([str(param) for param in self.children[0].address]) + ")"
			self.code = self.children[0].code + [self.address]
			block_code[self.block] += self.code

		elif astNode.name == "RETURN ":
			if not self.children:
				self.code = [("return",)]
			else:
				self.address = self.children[0].address
				self.code = self.children[0].code + [("return",self.address)]
			block_code[self.block] += self.code

		elif astNode.name in operator:
			self.address = 't' + str(t_id)
			t_id += 1
			self.code = self.children[0].code + self.children[1].code + [(self.address, '=', self.children[0].address, operator[astNode.name], self.children[1].address)]
	
		elif astNode.name == "UMINUS":
			self.address = 't' + str(t_id)
			t_id += 1
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
			block_code[self.children[0].block] = self.children[0].code
	
		elif astNode.name == "WHILE":
			self.code = []
			self.address = self.children[0].address
			self.block = self.children[0].block
			block_code[self.children[0].block] = self.children[0].code
	
		elif astNode.name == "STMLIST":
			self.code = []
			if len(self.children)>0:
				self.block = self.children[0].block
			for child in self.children:
				self.code += child.code

		else:
			raise Exception("Did not implement CFG for %s node"%(astNode.name,))

	def buildGraph(self, astNode, nextBlock = -1):
		global block_goto
		if nextBlock==-1:
			nextBlock = block_id

		if astNode.name=='IF':

			if len(self.children)==3:
				ifTarget = self.children[1].block
				elseTarget = self.children[2].block
				if len(self.children[1].children)==0:
					ifTarget = nextBlock
				if len(self.children[2].children)==0:
					elseTarget = nextBlock
				block_goto[self.children[0].block] = (ifTarget, elseTarget, True, self.address)
				self.children[1].buildGraph(astNode.children[1], nextBlock)
				self.children[2].buildGraph(astNode.children[2], nextBlock)
			elif len(self.children)==2:
				ifTarget = self.children[1].block
				if len(self.children[1].children)==0:
					ifTarget = nextBlock
				block_goto[self.children[0].block] = (ifTarget, nextBlock, True, self.address)
				self.children[1].buildGraph(astNode.children[1], nextBlock)


		elif astNode.name=='WHILE':

			if len(self.children)==2:
				block_goto[self.children[0].block] = (self.children[1].block, nextBlock, True, self.address)
				self.children[1].buildGraph(astNode.children[1], self.children[0].block)
			else:
				block_goto[self.children[0].block] = (self.children[0].block, nextBlock, True, self.address)

		elif astNode.name=='STMLIST':

			for i in range(len(self.children)):
				if i<len(self.children)-1:
					self.children[i].buildGraph(astNode.children[i], self.children[i+1].block)
				else:
					self.children[i].buildGraph(astNode.children[i], nextBlock)
		else:
			block_goto[self.block] = (nextBlock, nextBlock, False)


	def to_str(self, start_block):
		global block_code, block_goto, block_id
		cfg_str = ''
		for block,code in block_code.items():
			if (block < start_block):
				continue
			cfg_str += "<bb " + str(block) + ">\n"
			for line in code:
				cfg_str += ' '.join([str(word) for word in line])+'\n'
			t = block_goto[block]
			if t is not None:
				if t[2]:
					cfg_str += 'if(%s) goto <bb %d>\nelse goto <bb %d>\n'%(t[3], t[0], t[1])
				else:
					cfg_str += 'goto <bb %d>\n'%(t[0],)
			cfg_str += '\n'
		return cfg_str
	
class AST_Node:
	def __init__(self,name,children=None, value=None):
		
		self.name = name
		self.value = value
		
		if children is not None:
			self.children = children
			self.leaf = False
		
		else:
			self.children = []
			self.leaf = True
	
	def __str__(self):
		
		if self.leaf:
			return '\n' + self.name+'('+str(self.value)+')'

		elif self.name == 'FUNCTION':

			if self.children[1][0]!='main':

				ast_str = '\n'
				ast_str += 'FUNCTION %s\n'%(self.children[1][0])
				ast_str += 'PARAMS (%s)\n'%(', '.join([param.type + ' ' + '*'*param.indirection + param.name for param in self.children[2]]))
				ast_str += 'RETURNS %s'%('*'*self.children[1][1]+self.children[0])
				ast_str += str(self.children[3]).replace('\n', '\n\t')
				ast_str += str(self.children[4])+'\n'
				return ast_str

			else:

				ast_str = '\n'
				ast_str = 'Function Main\n'
				ast_str += 'PARAMS(%s) \n'%(', '.join([param.type + ' ' + '*'*param.indirection + param.name for param in self.children[2]]))
				ast_str += 'RETURNS %s'%(self.children[0]+'*'*self.children[1][1])
				ast_str += str(self.children[3]).replace('\n', '\n\t')+'\n'
				return ast_str

		elif self.name == 'FCALL':

			ast_str = '\nCALL %s( \n'%(self.value)
			args = self.children[0].children
			args_str = '\n,'.join([str(arg) for arg in args])
			ast_str += args_str.replace('\n','\n\t').strip('\n')
			ast_str += '\n )'
			return ast_str

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
	"""program : global_stmt_list"""
	symfile.write(str(current_ST_node))
	print("Successfully Parsed")

def p_global_stmt_list(p):
	"""global_stmt_list : empty
		| global_stmt global_stmt_list"""

def p_global_stmt(p):
	"""global_stmt : declaration
		| function"""

def p_function(p):
	"""function : VOID function_var LPAREN paramlist RPAREN function_dummy LBRACE function_body RBRACE
		| DATA_TYPE function_var LPAREN paramlist RPAREN function_dummy LBRACE function_body RBRACE
		| DATA_TYPE function_var LPAREN paramlist RPAREN function_proto_dummy SEMICOLON
		| VOID function_var LPAREN paramlist RPAREN function_proto_dummy SEMICOLON"""
	global current_ST_node, block_id
	current_ST_node = current_ST_node.parent
	if p[1]=='void' and p[2][1]>0:
		print('void' + '*'*p[2][1] + ' not allowed in function return type')
		exit(1)
	if len(p)>8:
		if p[6].return_type.type!=p[8][1].data_type.type or p[6].return_type.indirection != p[8][1].data_type.indirection:
			print('Return type does not match with definition: line %d'%(p.lexer.lineno))
			exit(1)
		p[0] = AST_Node('FUNCTION', children=[p[1], p[2], p[4], p[8][0], p[8][1]])
		return_ast = p[8][1]
		function_name = p[2][0]
		astfile.write(str(p[0]))
		start_block = block_id + 1
		ast_node = p[8][0]
		cfg_node = CFG_Node(ast_node, new_block=True, parent = '')
		cfg_return = CFG_Node(return_ast, new_block = True, parent = '')
		cfg_node.buildGraph(ast_node)

		function_params = current_ST_node.symbols[function_name].getParams()
		current_ST_node.symbols[function_name].scope.calculate_offsets()
		cfgfile.write("\nfunction " + function_name + "(" + function_params + ")\n")
		cfgfile.write(cfg_node.to_str(start_block))

def p_function_var(p):
	"""function_var : IDENTIFIER
		| ASTERISK function_var"""
	if p[1]=='*':
		p[0] = (p[2][0], p[2][1]+1)
	else:
		p[0] = (p[1], 0)

def p_paramlist(p):
	"""paramlist : DATA_TYPE decl_var 
		| paramlist COMMA DATA_TYPE decl_var
		| empty"""
	if len(p)==2:
		p[0] = []
	elif len(p)==3:
		p[0] = [Type(p[2][0], p[2][1], p[1], 4, None, is_param=True)]
	else:
		p[0] = p[1] + [Type(p[4][0], p[4][1], p[3], 4, None, is_param=True)]

def p_function_body(p):
	"""function_body : statement_list return_statement"""	
	p[0] = (p[1],p[2])

def p_return_statement(p):
	"""return_statement : RETURN expression SEMICOLON
		| RETURN SEMICOLON
		| empty"""
	if len(p)==4:
		p[0] = AST_Node('RETURN ', children=[p[2]])
		p[0].data_type = Type(None, p[2].data_type[1], p[2].data_type[0], 4, 0)

		if hasattr(p[2],"is_identifier") and p[2].data_type[1] == 0:
			print('direct use of non pointer variable %d'%(p.lexer.lineno,))
			exit(1)

	else:
		p[0] = AST_Node('RETURN ', children=[])
		p[0].data_type = Type(None, 0, 'void', 4, 0)

def p_function_dummy(p):
	"""function_dummy : empty"""
	global current_ST_node
	if p[-4][0] in current_ST_node.symbols and not current_ST_node.symbols[p[-4][0]].is_proto:
		print('Declared again: %s'%(p[-4][0],))
		exit(1)
	else:
		return_type = Type(None, p[-4][1], p[-5], 4, 0)
		if p[-4][0] in current_ST_node.symbols:
			known_params = current_ST_node.symbols[p[-4][0]].params
			known_return_type = current_ST_node.symbols[p[-4][0]].return_type
			if known_return_type.type!=return_type.type or known_return_type.indirection!=return_type.indirection:
				print('Return type not matching with prototype: %s'%(p[-4][0],))
				exit(1)
			else:
				params_match = True

				if len(known_params)!=len(p[-2]):
					params_match = False
				i = 0
				while i<len(known_params) and i<len(p[-2]):
					if known_params[i].type!=p[-2][i].type or known_params[i].indirection!=p[-2][i].indirection:
						params_match = False
						break
					i += 1
				if not params_match:
					print('Parameter %d not matching with prototype: %s'%(i,p[-4][0],))
					exit(1)


		type = Type(p[-4][0], p[-4][-1], 'FUNCTION', 4, 0)
		scope = Scope(parent=current_ST_node, function=type)
		for param in p[-2]:
			scope.symbols[param.name] = param
		type.setFunctionProperties(scope, p[-2], return_type, is_proto=False)
		param_same, param_name, prev_param = False, None, set()
		for param in p[-2]:
			param_name = param.name
			if param_name in prev_param:
				param_same = True
				break
			prev_param.add(param_name)
		if param_same:
			print('Parameter %s declared multiple time, line number %d\n'%(param_name,p.lexer.lineno,))
			exit(1)
		current_ST_node.symbols[p[-4][0]] = type
		current_ST_node = scope
		p[0] = type


def p_function_proto_dummy(p):
	"""function_proto_dummy : empty"""
	global current_ST_node
	if p[-4][0] in current_ST_node.symbols:
		print('Declared again: %s'%(p[-4],))
		exit(1)
	else:
		scope = Scope(parent=current_ST_node)
		type = Type(p[-4][0], None, 'FUNCTION', 4, 0)
		return_type = Type(None, p[-4][1], p[-5], 4, 0)
		type.setFunctionProperties(scope, p[-2], return_type, is_proto=True)
		current_ST_node.symbols[p[-4][0]] = type
		current_ST_node = scope

def p_statement_list(p):
	"""statement_list : statement_list statement
		| empty"""
	if p[1]=='':
		p[0] = AST_Node("STMLIST", children=[])
	else:
		p[0] = AST_Node("STMLIST", children=p[1].children+p[2])

def p_statement(p):
	"""statement : declaration
		| assignment
		| function_call SEMICOLON
		| while_block
		| if_else_block"""
	if p[1].name=='FCALL':
		p[1].is_statement = True
	if p[1].name=='DECL':
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
	"""declaration : DATA_TYPE decl_var_list SEMICOLON"""
	for var in p[2]:
		if var[0] in current_ST_node.symbols:
			print('Variable declared again %s'%(var[0],))
			exit(1)
		else:
			current_ST_node.symbols[var[0]] = Type(var[0], var[1], p[1], 4, 0)
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
	p[0].data_type = (p[2].data_type[0], p[2].data_type[1]-1)
	if p[0].data_type[1]<0:
		print("Too much indirection: line no  '%d' " % (p.lexer.lineno,))
		exit(1)
def p_scalar_var(p):
	"""scalar_var : IDENTIFIER
		| AMPERSAND IDENTIFIER"""
	if p[1] == '&':
		p[0] = AST_Node("ADDR", children = [AST_Node("VAR", value = p[2])])
		var_name = p[2]
	else:
		p[0] = AST_Node("VAR", value = p[1])
		var_name = p[1]

	checked_node = current_ST_node
	while checked_node is not None and var_name not in checked_node.symbols:
		checked_node = checked_node.parent
	if checked_node is None:
		print('Unknown symbol %s'%(var_name,))
		exit(1)

	if p[1]=='&':
		p[0].data_type = (checked_node.symbols[var_name].type, checked_node.symbols[var_name].indirection+1)
		p[0].is_identifier = False
	else:
		p[0].data_type = (checked_node.symbols[var_name].type, checked_node.symbols[var_name].indirection)
		p[0].is_identifier = True

def p_assignment(p):
	"""assignment : pointer_var EQUALS expression SEMICOLON
		| IDENTIFIER EQUALS expression SEMICOLON"""
	if isinstance(p[1], str):
		var_name = p[1]
		p[1] = AST_Node("VAR", value=p[1])
		checked_node = current_ST_node
		while checked_node is not None and var_name not in checked_node.symbols:
			checked_node = checked_node.parent
		if checked_node is None:
			print('Unknown symbol %s'%(var_name,))
			exit(1)
		p[1].data_type = (checked_node.symbols[var_name].type, checked_node.symbols[var_name].indirection) 

	if p[1].data_type!=p[3].data_type:
		print('Type mismatch at %d'%(p.lexer.lineno,))
		exit(1)

	if  hasattr(p[3],"is_identifier"):
		if p[3].is_identifier:
			print('direct use of non pointer variable %d'%(p.lexer.lineno,))
			exit(1)


	p[0] = AST_Node("ASGN", children = [p[1],p[3]])


def p_expression_add(p):
	"""expression : expression PLUS expression"""
	p[0] = AST_Node("PLUS", children = [p[1],p[3]])
	if p[1].data_type!=p[3].data_type:
		print('Type mismatch at %d'%(p.lexer.lineno,))
		exit(1)
	if p[1].data_type[1] != 0:
		print('Pointer operation not allowed %d'%(p.lexer.lineno,))
		exit(1)
	if hasattr(p[1],"is_identifier") or hasattr(p[3],"is_identifier"):
		print('direct use of non pointer variable %d'%(p.lexer.lineno,))
		exit(1)
	p[0].data_type = p[3].data_type

def p_expression_subtract(p):
	"""expression : expression MINUS expression"""
	p[0] = AST_Node("MINUS", children = [p[1],p[3]])
	if p[1].data_type!=p[3].data_type:
		print('Type mismatch at %d'%(p.lexer.lineno,))
		exit(1)
	if p[1].data_type[1] != 0:
		print('Pointer operation not allowed %d'%(p.lexer.lineno,))
		exit(1)
	if hasattr(p[1],"is_identifier") or hasattr(p[3],"is_identifier"):
		print('direct use of non pointer variable %d'%(p.lexer.lineno,))
		exit(1)
	p[0].data_type = p[3].data_type

def p_expression_parenthesis(p):
	"""expression : LPAREN expression RPAREN"""
	p[0] = p[2]

def p_expression_multiply(p):
	"""expression : expression ASTERISK expression"""
	p[0] = AST_Node("MUL", children = [p[1],p[3]])
	if p[1].data_type!=p[3].data_type:
		print('Type mismatch at %d'%(p.lexer.lineno,))
		exit(1)
	if p[1].data_type[1] != 0:
		print('Pointer operation not allowed %d'%(p.lexer.lineno,))
		exit(1)
	if hasattr(p[1],"is_identifier") or hasattr(p[3],"is_identifier"):
		print('direct use of non pointer variable %d'%(p.lexer.lineno,))
		exit(1)
	p[0].data_type = p[3].data_type

def p_expression_divide(p):
	"""expression : expression FSLASH expression"""
	p[0] = AST_Node("DIV", children = [p[1],p[3]])
	if p[1].data_type!=p[3].data_type:
		print('Type mismatch at %d'%(p.lexer.lineno,))
		exit(1)
	if p[1].data_type[1] != 0:
		print('Pointer operation not allowed %d'%(p.lexer.lineno,))
		exit(1)
	if hasattr(p[1],"is_identifier") or hasattr(p[3],"is_identifier"):
		print('direct use of non pointer variable %d'%(p.lexer.lineno,))
		exit(1)
	p[0].data_type = p[3].data_type

def p_expression_negation(p):
	"""expression : MINUS expression %prec UMINUS"""
	p[0] = AST_Node("UMINUS", children = [p[2]])
	p[0].data_type = p[2].data_type
	if p[2].data_type[1] != 0:
		print('Pointer operation not allowed %d'%(p.lexer.lineno,))
		exit(1)
	if hasattr(p[2],"is_identifier"):
		print('direct use of non pointer variable %d'%(p.lexer.lineno,))
		exit(1)

def p_expression_function_call(p):
	"""expression : function_call"""
	p[0] = p[1]

def p_function_call(p):
	"""function_call : IDENTIFIER LPAREN arglist RPAREN
		| IDENTIFIER LPAREN RPAREN
		| ASTERISK function_call"""
	if len(p)!=3:
		if len(p)==5:
			p[0] = AST_Node("FCALL", children = [p[3]], value = p[1])
			p[0].is_statement = False
			arguments = p[3].children
		else:
			arguments = []
			p[0] = AST_Node("FCALL", children = [AST_Node("ARGLIST", children=[])], value = p[1])
			p[0].is_statement = False

		checked_node = current_ST_node
		func_name = p[1]
		while checked_node is not None and func_name not in checked_node.symbols:
			checked_node = checked_node.parent
		if checked_node is None:
			print('Unknown symbol %s'%(func_name,))
			exit(1)
		p[0].data_type = (checked_node.symbols[func_name].return_type.type, checked_node.symbols[func_name].return_type.indirection)
		params = checked_node.symbols[func_name].params
		if len(arguments)!=len(params):
			print("Wrong number of arguments: line no  '%d' " % (p.lexer.lineno,))
			exit(1)
		else:
			for i in range(len(arguments)):
				if arguments[i].data_type[0]!=params[i].type or arguments[i].data_type[1]!=params[i].indirection:
					print("Wrong %dth argument type: line no  '%d' " % ( i+1, p.lexer.lineno,))
					exit(1)

	else:
		p[0] = AST_Node('DEREF', children=[p[2]])
		p[0].data_type = (p[2].data_type[0], p[2].data_type[1]-1)
		if p[0].data_type[1]<0:
			print("Too much indirection: line no  '%d' " % (p.lexer.lineno,))
			exit(1)
		

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
	if p[1].data_type!=p[3].data_type:
		print('Type mismatch at %d'%(p.lexer.lineno,))
		exit(1)
	if p[1].data_type[1] != 0:
		print('Pointer operation not allowed %d'%(p.lexer.lineno,))
		exit(1)
	if hasattr(p[1],"is_identifier") or hasattr(p[3],"is_identifier"):
		print('direct use of non pointer variable %d'%(p.lexer.lineno,))
		exit(1)
	p[0].data_type = ('bool', 0)

def p_condition_ne(p):
	"""condition : expression NE expression"""
	p[0] = AST_Node("NE", children = [p[1],p[3]])
	if p[1].data_type!=p[3].data_type:
		print('Type mismatch at %d'%(p.lexer.lineno,))
		exit(1)
	if p[1].data_type[1] != 0:
		print('Pointer operation not allowed %d'%(p.lexer.lineno,))
		exit(1)
	if hasattr(p[1],"is_identifier") or hasattr(p[3],"is_identifier"):
		print('direct use of non pointer variable %d'%(p.lexer.lineno,))
		exit(1)
	p[0].data_type = ('bool', 0)

def p_condition_lt(p):
	"""condition : expression LT expression"""
	p[0] = AST_Node("LT", children = [p[1],p[3]])
	if p[1].data_type!=p[3].data_type:
		print('Type mismatch at %d'%(p.lexer.lineno,))
		exit(1)
	if p[1].data_type[1] != 0:
		print('Pointer operation not allowed %d'%(p.lexer.lineno,))
		exit(1)
	if hasattr(p[1],"is_identifier") or hasattr(p[3],"is_identifier"):
		print('direct use of non pointer variable %d'%(p.lexer.lineno,))
		exit(1)
	p[0].data_type = ('bool', 0)

def p_condition_gt(p):
	"""condition : expression GT expression"""
	p[0] = AST_Node("GT", children = [p[1],p[3]])
	if p[1].data_type!=p[3].data_type:
		print('Type mismatch at %d'%(p.lexer.lineno,))
		exit(1)
	if p[1].data_type[1] != 0:
		print('Pointer operation not allowed %d'%(p.lexer.lineno,))
		exit(1)
	if hasattr(p[1],"is_identifier") or hasattr(p[3],"is_identifier"):
		print('direct use of non pointer variable %d'%(p.lexer.lineno,))
		exit(1)
	p[0].data_type = ('bool', 0)

def p_condition_lte(p):
	"""condition : expression LTE expression"""
	p[0] = AST_Node("LE", children = [p[1],p[3]])
	if p[1].data_type!=p[3].data_type:
		print('Type mismatch at %d'%(p.lexer.lineno,))
		exit(1)
	if p[1].data_type[1] != 0:
		print('Pointer operation not allowed %d'%(p.lexer.lineno,))
		exit(1)
	if hasattr(p[1],"is_identifier") or hasattr(p[3],"is_identifier"):
		print('direct use of non pointer variable %d'%(p.lexer.lineno,))
		exit(1)
	p[0].data_type = ('bool', 0)

def p_condition_gte(p):
	"""condition : expression GTE expression"""
	p[0] = AST_Node("GE", children = [p[1],p[3]])
	if p[1].data_type!=p[3].data_type:
		print('Type mismatch at %d'%(p.lexer.lineno,))
		exit(1)
	if p[1].data_type[1] != 0:
		print('Pointer operation not allowed %d'%(p.lexer.lineno,))
		exit(1)
	if hasattr(p[1],"is_identifier") or hasattr(p[3],"is_identifier"):
		print('direct use of non pointer variable %d'%(p.lexer.lineno,))
		exit(1)
	p[0].data_type = ('bool', 0)

def p_condition_land(p):
	"""condition : condition AMPERSAND AMPERSAND condition %prec LAND"""
	p[0] = AST_Node("AND", children = [p[1], p[4]])
	if p[1].data_type!=p[4].data_type:
		print('Type mismatch at %d'%(p.lexer.lineno,))
		exit(1)
	if p[1].data_type[1] != 0:
		print('Pointer operation not allowed %d'%(p.lexer.lineno,))
		exit(1)
	if hasattr(p[1],"is_identifier") or hasattr(p[3],"is_identifier"):
		print('direct use of non pointer variable %d'%(p.lexer.lineno,))
		exit(1)
	p[0].data_type = ('bool', 0)

def p_condition_lor(p):
	"""condition : condition PIPE PIPE condition %prec LOR"""
	p[0] = AST_Node("OR", children = [p[1], p[4]])
	if p[1].data_type!=p[4].data_type:
		print('Type mismatch at %d'%(p.lexer.lineno,))
		exit(1)
	if p[1].data_type[1] != 0:
		print('Pointer operation not allowed %d'%(p.lexer.lineno,))
		exit(1)
	if hasattr(p[1],"is_identifier") or hasattr(p[3],"is_identifier"):
		print('direct use of non pointer variable %d'%(p.lexer.lineno,))
		exit(1)
	p[0].data_type = ('bool', 0)

def p_condition_parenthesis(p):
	"""condition : LPAREN condition RPAREN"""
	p[0] = p[2]

def p_expression_base_constant(p):
	"""expression : CONSTANT"""
	p[0] = AST_Node("CONST", value = p[1])
	if isinstance(p[1], int):
		p[0].data_type = ('int', 0)
	elif isinstance(p[1], float):
		p[0].data_type = ('float', 0)

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
symfile.close()
