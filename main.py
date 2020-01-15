#!/usr/bin/env python
import sys
import pickle	
import string

from regex import RegEx
from regular_expression import RegularExpression
from nfa import NFA
from dfa import DFA

alphabet = list(string.ascii_lowercase) + list(string.ascii_uppercase) + list(string.digits)
special_characters = ['|', '.', '*', '+', '[', ']', '(', ')', '{', '}', ',', '-', '?']
digits = list(string.digits)
letters = list(string.ascii_lowercase) + list(string.ascii_uppercase)

EMPTY_STRING = 0
SYMBOL_SIMPLE = 1
SYMBOL_ANY = 2
SYMBOL_SET = 3
MAYBE = 4
STAR = 5
PLUS = 6
RANGE = 7
CONCATENATION = 8
ALTERNATION = 9

# pentru Expresii Regulate
# EMPTY_SET = 0
# EMPTY_STRING = 1
# SYMBOL = 2
# STAR = 3
# CONCATENATION = 4
# ALTERNATION = 5

def rename_states(target, reference):
    off = max(reference.states) + 1
    target.start_state += off
    target.states = set(map(lambda s: s + off, target.states))
    target.final_states = set(map(lambda s: s + off, target.final_states))
    new_delta = {}
    for (state, symbol), next_states in target.delta.items():
        new_next_states = set(map(lambda s: s + off, next_states))
        new_delta[(state + off, symbol)] = new_next_states

    target.delta = new_delta


def new_states(*nfas):
    state = 0
    for nfa in nfas:
        m = max(nfa.states)
        if m >= state:
            state = m + 1

    return state, state + 1

def Merge(dict1, dict2): 
    res = {**dict1, **dict2} 
    return res
  
def intersection(lst1, lst2): 
    lst3 = [value for value in lst1 if value in lst2] 
    return lst3

def Union(lst1, lst2): 
    final_list = list(set(lst1) | set(lst2)) 
    return final_list 

def re_to_nfa(re):
    """Convert a Regular Expression to a Nondeterminstic Finite Automaton"""
    if re.type == 0:
      nfa = NFA("", {0,1}, 0, {1}, {})
    if re.type == 1:
      nfa = NFA("", {0, 1}, 0, {1}, {(0, ""): {1}})
    if re.type == 2:
      nfa = NFA(re.symbol, {0, 1}, 0, {1}, {(0, re.symbol): {1}})
    if re.type == 5:
      if re.lhs.type == 2 and re.rhs.type == 2:
        nfa = NFA(re.lhs.symbol+re.rhs.symbol, {0,1,2,3,4,5}, 0, {3}, {(0, ""):{1,4}, (1, re.rhs.symbol):{2}, 
                 (2, ""):{3}, (4, re.lhs.symbol):{5}, (5, ""):{3}})
      else:
        nfa1 = re_to_nfa(re.lhs)
        nfa2 = re_to_nfa(re.rhs)
        rename_states(nfa1, nfa2);
        new_state1, new_state2 = new_states(nfa1, nfa2)
        if (next(iter(nfa2.final_states)), "") in nfa2.delta:
        	final_st = nfa2.delta[(next(iter(nfa2.final_states)), "")]
        	nfa = NFA(Union(nfa1.alphabet,nfa2.alphabet), nfa1.states.union(nfa2.states).union({new_state1, new_state2}), 
                  new_state1, {new_state2}, Merge((Merge(nfa1.delta, nfa2.delta)),{(new_state1, "") : {nfa1.start_state, nfa2.start_state},
                  (next(iter(nfa1.final_states)), "") : {new_state2},  (next(iter(nfa2.final_states)), "") : {new_state2}.union(final_st)}))
        else:
        	nfa = NFA(Union(nfa1.alphabet,nfa2.alphabet), nfa1.states.union(nfa2.states).union({new_state1, new_state2}), 
                  new_state1, {new_state2}, Merge((Merge(nfa1.delta, nfa2.delta)),{(new_state1, "") : {nfa1.start_state, nfa2.start_state},
                  (next(iter(nfa1.final_states)), "") : {new_state2},  (next(iter(nfa2.final_states)), "") : {new_state2}}))
    
    if re.type == 4:
      if re.lhs.type == 2 and re.rhs.type == 2:
        nfa = NFA(re.lhs.symbol+re.rhs.symbol, {0,1,2,3,4,5}, 0, {5}, {(0, ""): {1}, (1, re.lhs.symbol): {2},
                  (2, ""): {3}, (3, re.rhs.symbol): {4}, (4, ""): {5}})
      else:
        nfa1 = re_to_nfa(re.lhs)
        nfa2 = re_to_nfa(re.rhs)
        rename_states(nfa1, nfa2)
        new_state1, new_state2 = new_states(nfa1, nfa2)
        if (next(iter(nfa2.final_states)), "") in nfa2.delta:
	        final_st = nfa2.delta[(next(iter(nfa2.final_states)), "")]
	        nfa = NFA(Union(nfa1.alphabet,nfa2.alphabet), nfa1.states.union(nfa2.states).union({new_state1, new_state2}), 
	                  new_state1, {new_state2}, Merge((Merge(nfa1.delta, nfa2.delta)),{(new_state1, "") : {nfa1.start_state},
	                  (next(iter(nfa1.final_states)), ""): {nfa2.start_state}, 
	                  (next(iter(nfa2.final_states)), "") : {new_state2}.union(final_st)}))
        else:
            nfa = NFA(Union(nfa1.alphabet,nfa2.alphabet), nfa1.states.union(nfa2.states).union({new_state1, new_state2}), 
          		new_state1, {new_state2}, Merge((Merge(nfa1.delta, nfa2.delta)),{(new_state1, "") : {nfa1.start_state},
          		(next(iter(nfa1.final_states)), ""): {nfa2.start_state}, 
          		(next(iter(nfa2.final_states)), "") : {new_state2}}))
    if re.type == 3:
      if re.lhs.type == 2:
        nfa = NFA(re.lhs.symbol, {0,1,2,3}, 0, {3}, {(3, ""):{0}, (0, ""): {1,3}, (1, re.lhs.symbol): {2}, (2, ""): {3}})
      else:
        nfa1 = re_to_nfa(re.lhs)
        new_state1, new_state2 = new_states(nfa1)
        #adauga tranz final_state -> start_state
        nfa = NFA(nfa1.alphabet, nfa1.states.union({new_state1, new_state2}), new_state1, {new_state2}, 
              Merge(nfa1.delta, {(new_state1, "") : {nfa1.start_state, new_state2}, 
              	(next(iter(nfa1.final_states)), ""): {new_state2, nfa1.start_state}}))
    return nfa

def parseRegEx(regex_string):
	count = 0
	for i in regex_string:
		#numar setul de paranteze
		if(i == '('):
			count = count + 1
	if regex_string == "":
		#sirul vid
		parsed_regex = RegEx(EMPTY_STRING)
		return parsed_regex
	
	if regex_string[0] == "." and len(regex_string) == 1:
		parsed_regex = RegEx(SYMBOL_ANY)
		return parsed_regex
	
	if regex_string[0] in alphabet and len(regex_string) == 1:
		#expresii de tipul {a}, {b}..
		parsed_regex = RegEx(SYMBOL_SIMPLE, regex_string[0])
		return parsed_regex

	if regex_string[0] in alphabet and regex_string[1] in alphabet:
		if len(regex_string) == 2:
			#expresii de tipul ab, aa, bb..
			parsed_regex = RegEx(CONCATENATION, RegEx(SYMBOL_SIMPLE, regex_string[0]), 
				RegEx(SYMBOL_SIMPLE, regex_string[1]))
			return parsed_regex
		else:
			#expresii de tipul ab*, ab+, ab?..
			if regex_string[2] == "*":
				parsed_regex = RegEx(CONCATENATION, RegEx(SYMBOL_SIMPLE, regex_string[0]), 
					RegEx(STAR, RegEx(SYMBOL_SIMPLE, regex_string[1])))
				return parsed_regex
			if regex_string[2] == "?":
				parsed_regex = RegEx(CONCATENATION, RegEx(SYMBOL_SIMPLE, regex_string[0]), 
					RegEx(MAYBE, RegEx(SYMBOL_SIMPLE, regex_string[1])))
				return parsed_regex
			if regex_string[2] == "+":
				parsed_regex = RegEx(CONCATENATION, RegEx(SYMBOL_SIMPLE, regex_string[0]), 
					RegEx(PLUS, RegEx(SYMBOL_SIMPLE, regex_string[1])))
				return parsed_regex
			#expresii de tipul aa|bb
			if regex_string[2] == "|":
				parsed_regex = RegEx(ALTERNATION, RegEx(CONCATENATION, 
					RegEx(SYMBOL_SIMPLE, regex_string[0]), RegEx(SYMBOL_SIMPLE, regex_string[1])),
					parseRegEx(regex_string[3:]))
				return parsed_regex 

	if regex_string[0] in alphabet and regex_string[1] in special_characters and len(regex_string) == 2:
		#expresii de tipul a*, b+
		if regex_string[1] == '?':
			parsed_regex = RegEx(MAYBE, RegEx(SYMBOL_SIMPLE, regex_string[0]))
			return parsed_regex
		if regex_string[1] == '*':
			parsed_regex = RegEx(STAR, RegEx(SYMBOL_SIMPLE, regex_string[0]))
			return parsed_regex
		if regex_string[1] == '+':
			parsed_regex = RegEx(PLUS, RegEx(SYMBOL_SIMPLE, regex_string[0]))
			return parsed_regex
	
	if regex_string[0] in alphabet and regex_string[1] in special_characters:
		#expresii de tipul a|b
		first = regex_string[0]
		if regex_string[1] == '|':
			regex_string = regex_string[2:]
			parsed_regex = RegEx(ALTERNATION, RegEx(SYMBOL_SIMPLE, first), parseRegEx(regex_string))
			return parsed_regex
		if regex_string[1] == '?':
			regex_string = regex_string[2:]
			parsed_regex = RegEx(CONCATENATION,(RegEx(MAYBE, 
				RegEx(SYMBOL_SIMPLE, first))), parseRegEx(regex_string))
			return parsed_regex
	
	if count > 1:
		#expresii cu un numar de perechi de paranteze > 1
		paranthesis_nr = 0
		exp1 = ""
		exp2 = ""
		exp3 = ""
		for i in regex_string:
			if i == "(":
				paranthesis_nr = paranthesis_nr + 1
			if paranthesis_nr == count and i != ")" and i != "(":
				exp1 = exp1 + i
			if i == ")" and paranthesis_nr == count:
				break
		paranthesis_nr = 0
		for i in regex_string:
			if i == "(":
				paranthesis_nr = paranthesis_nr + 1
			if paranthesis_nr == count - 1 and i != ")" and i != "(":
				exp2 = exp2 + i
			if i == ")" and paranthesis_nr == count - 1:
				break
		paranthesis_nr = 0
		for i in regex_string:
			if i == "(":
				paranthesis_nr = paranthesis_nr + 1
			if paranthesis_nr == count - 2 and i != ")" and i != "(":
				exp3 = exp3 + i
			if i == ")" and paranthesis_nr == count - 2:
				break
		parsed_regex1 = RegEx(CONCATENATION, parseRegEx(exp2), parseRegEx(exp1))
		if regex_string[len(regex_string) - 1] == "+":
			parsed_regex1 = RegEx(PLUS, parsed_regex1)
		parsed_regex = RegEx(CONCATENATION, parseRegEx(exp3), parsed_regex1)
		return parsed_regex
	
	if regex_string[0] == '(' or regex_string[1] == '(':
		#expresii cu o singura pereche de paranteze
		newString = ""
		for i in regex_string:
			if i != '(' and i != ')':
				newString = newString + i
			if i == ')':
				break
		if regex_string[0] in alphabet:
			newString = newString[1:]
			parsed_regex = parseRegEx(newString)
			parsed_regex = RegEx(CONCATENATION, RegEx(SYMBOL_SIMPLE, 
				regex_string[0]), parsed_regex)
		else:
			parsed_regex = parseRegEx(newString)

		if len(newString) + 2 == len(regex_string):
			return parsed_regex
		else:
			if regex_string[len(newString) + 2] == '+':
				parsed_regex = RegEx(PLUS, parsed_regex)
			if regex_string[len(newString) + 2] == '*':
				parsed_regex = RegEx(STAR, parsed_regex)
			if regex_string[len(newString) + 2] == '?':
				parsed_regex = RegEx(MAYBE, parsed_regex)
			if regex_string[len(newString) + 2] in alphabet:
				parsed_regex = RegEx(CONCATENATION, parsed_regex, 
					RegEx(SYMBOL_SIMPLE, regex_string[len(newString) + 2]))
			if regex_string[0] in alphabet:
				if len(regex_string) > len(newString) + 3:
					if regex_string[len(newString) + 3] in alphabet:
						parsed_regex = RegEx(CONCATENATION, parsed_regex, 
							RegEx(SYMBOL_SIMPLE, regex_string[len(newString) + 3]))
			return parsed_regex

	if regex_string[0] == '[':
		#expresii de tipul [a-z], [abc0-9]..
		if '-' in regex_string and len(regex_string) == 5 or len(regex_string) == 6:
			parsed_regex = RegEx(SYMBOL_SET, {(regex_string[1],regex_string[3])})
			if len(regex_string) == 6:
				if regex_string[5] == "*":
					parsed_regex = RegEx(STAR, parsed_regex)
			return parsed_regex
		if '-' in regex_string and len(regex_string) > 6:
			count = 0
			for i in regex_string:
				if i == '-':
					count = count + 1
			if count == 1:
				symbols = ""
				_range_ = ""
				for i in range(len(regex_string)):
					if regex_string[i] in digits or regex_string[i] in letters:
						if regex_string[i] not in _range_:
							symbols += regex_string[i]
					if regex_string[i] == '-':
						_range_ += symbols[len(symbols) - 1]
						_range_ += regex_string[i + 1]
						symbols = symbols[:-1]
				parsed_regex = RegEx(SYMBOL_SET, {symbols[0], symbols[1], symbols[2], 
					(_range_[0], _range_[1])})
				return parsed_regex
			if count == 2:
				if len(regex_string) == 8:
					parsed_regex = RegEx(SYMBOL_SET, {(regex_string[1], regex_string[3]),
						(regex_string[4], regex_string[6])})
					return parsed_regex
				else:
					symbols = ""
					_range1_ = ""
					_range2_ = ""
					for i in range(len(regex_string)):
						if regex_string[i] in digits or regex_string[i] in letters:
							if regex_string[i] not in _range1_ and regex_string[i] not in _range2_:
								symbols += regex_string[i]
						if regex_string[i] == '-':
							if _range1_ == "":
								_range1_ += symbols[len(symbols) - 1]
								_range1_ += regex_string[i + 1]
								symbols = symbols[:-1]
							else:
								_range2_ += symbols[len(symbols) - 1]
								_range2_ += regex_string[i + 1]
								symbols = symbols[:-1]
					parsed_regex = RegEx(SYMBOL_SET, {symbols[0], symbols[1], symbols[2], 
					(_range1_[0], _range1_[1]), (_range2_[0], _range2_[1])})
					return parsed_regex;
		if '-' not in regex_string:
			newString = ""
			for i in regex_string:
				if i != '[' and i != ']':
					newString = newString + i
				if i == ']':
					break
			parsed_regex = RegEx(SYMBOL_SET, newString)
			return parsed_regex
	
	if regex_string[0] in alphabet and regex_string[1] == "{":
		#expresii de tipul a{2,}, a{,2}..
		if regex_string[2] in digits and len(regex_string) > 4:
			if regex_string[4] in digits:
				parsed_regex = RegEx(RANGE, RegEx(SYMBOL_SIMPLE, regex_string[0]), 
						(int(regex_string[2]), int(regex_string[4])))
				return parsed_regex
		if regex_string[2] in string.digits:
			if(regex_string[3] == "}"):
				parsed_regex = RegEx(RANGE, RegEx(SYMBOL_SIMPLE, regex_string[0]), 
					(int(regex_string[2]), int(regex_string[2])))
				return parsed_regex
			else:
				parsed_regex = RegEx(RANGE, RegEx(SYMBOL_SIMPLE, regex_string[0]), 
					(int(regex_string[2]), -1))
				return parsed_regex
		if regex_string[2] == ',' and regex_string[3] in digits:
			parsed_regex = RegEx(RANGE, RegEx(SYMBOL_SIMPLE, regex_string[0]), 
					(-1, int(regex_string[3])))
			return parsed_regex
		
def convertRegEx(parsed_regex):
	if parsed_regex.type == EMPTY_STRING:
		regular_expression = RegularExpression(1)
		return regular_expression
	if parsed_regex.type == SYMBOL_SIMPLE:
		regular_expression = RegularExpression(2, str(parsed_regex))
		return regular_expression
	# CONCATENATION = 8
	if parsed_regex.type == 8:
		regular_expression = RegularExpression(4, 
			convertRegEx(parsed_regex.lhs), convertRegEx(parsed_regex.rhs))
		return regular_expression
	# ALTERNATION = 9
	if parsed_regex.type == 9:
		regular_expression = RegularExpression(5, 
			convertRegEx(parsed_regex.lhs), convertRegEx(parsed_regex.rhs))
		return regular_expression
	# SYMBOL_ANY = 2
	if parsed_regex.type == 2:
		regular_expression = RegularExpression(1)
		for i in alphabet:
			symbol = RegEx(SYMBOL_SIMPLE, i)
			regular_expression = RegularExpression(5, regular_expression, 
				convertRegEx(symbol))
		return regular_expression
	# MAYBE = 4
	if parsed_regex.type == 4:
		aux = RegularExpression(1)
		regular_expression = RegularExpression(5, aux, 
				convertRegEx(parsed_regex.lhs))
		return regular_expression
	# STAR = 5
	if parsed_regex.type == 5:
		regular_expression = RegularExpression(3,
				convertRegEx(parsed_regex.lhs))
		return regular_expression
	# PLUS = 6
	if parsed_regex.type == 6:
		aux = convertRegEx(parsed_regex.lhs)
		aux2 = RegularExpression(3, aux)
		regular_expression = RegularExpression(4, aux, aux2)
		return regular_expression
	# RANGE = 8
	if parsed_regex.type == 7:
		x,y = parsed_regex.range
		if x == y:
			regular_expression = convertRegEx(parsed_regex.lhs)
			for i in range(x - 1):
				aux = convertRegEx(parsed_regex.lhs)
				regular_expression = RegularExpression(4, 
					regular_expression, aux)
			return regular_expression
		if x == -1:
			regular_expression = RegularExpression(1)
			for i in range(y + 1):
				if i != 0:
					exp = RegEx(RANGE, parsed_regex.lhs, (i, i))
					regular_expression = RegularExpression(5,
						regular_expression, convertRegEx(exp))
			return regular_expression
		if y == -1:
			exp = RegEx(RANGE, parsed_regex.lhs, (x, x))
			star_exp = RegularExpression(3, convertRegEx(parsed_regex.lhs))
			regular_expression = RegularExpression(4, 
				convertRegEx(exp), star_exp)
			return regular_expression
		else:
			# intre x si y aparitii
			exp = RegEx(RANGE, parsed_regex.lhs, (x, x))
			regular_expression = convertRegEx(exp)
			for i in range(x + 1,y + 1):
				exp = RegEx(RANGE, parsed_regex.lhs, (i, i))
				regular_expression = RegularExpression(5, 
					regular_expression, convertRegEx(exp))
			return regular_expression
	# SYMBOL_SET = 3
	if parsed_regex.type == 3:
		regular_expression = None
		for i in parsed_regex.symbol_set:
			if type(i) is tuple:
				if i[0] in digits:
					_range_ = RegularExpression(2, str(int(i[0])+1))
					if regular_expression is not None:
						aux = RegularExpression(2, i[0])
						regular_expression = RegularExpression(5,
							regular_expression, aux)
					else:
						regular_expression = RegularExpression(2, i[0])
					for k in range(int(i[0]) + 2, int(i[1]) + 1):
						symb = RegularExpression(2, str(k))
						_range_ = RegularExpression(5, _range_,
							symb)
					regular_expression = RegularExpression(5, 
							 regular_expression, _range_)
				else:
					_range_ = RegularExpression(2,chr(ord(i[0]) + 1))
					if regular_expression is not None:
						aux = RegularExpression(2, i[0])
						regular_expression = RegularExpression(5,
							regular_expression, aux)
					else:
						regular_expression = RegularExpression(2, i[0])
					char = chr(ord(i[0]) + 2)
					while char <= i[1]:
						symb = RegularExpression(2, char)
						_range_ = RegularExpression(5, _range_,
							symb)
						char = chr(ord(char) + 1)
					regular_expression = RegularExpression(5, 
							regular_expression,_range_)
		count = 0
		for i in parsed_regex.symbol_set:
			if type(i) is not tuple:
				if count == 0:
					symbol = RegEx(SYMBOL_SIMPLE, i)
					reg_symbol = convertRegEx(symbol)
					if regular_expression is None:
						regular_expression = reg_symbol
				else:
					symbol = RegEx(SYMBOL_SIMPLE, i)
					reg_symbol = convertRegEx(symbol)
					regular_expression = RegularExpression(5, regular_expression, 
						reg_symbol)
			count = count + 1
		
		return regular_expression

def merge_dicts(x, y):
	z = x.copy()
	z.update(y)
	return z

#state = o lista de stari ex:[2,3]	
def get_transition(nfa, state):

	alphabet = nfa.alphabet
	delta = nfa.delta
	state_name = ""

	final = False

	for s in state:
		state_name += str(s)
	
	new_transition = dict()
	flag = False
	for l in alphabet:
		new_state = list()
		for s in state:
			for t in delta:
				if t[0] == s and t[1] == l:
					if delta[t] not in new_state:
						new_state += list(delta[t])
					if delta[t] not in state:
						state += list(delta[t])
		
		for e in new_state:
			for t in delta:
				if t[0] == e and t[1] == "":
					#daca inchidere eps e una din starile initiale ne trebuie tranz
					#catre starea respectiva
					dict_d = list(delta[t])
					for d in dict_d:
						if d in state:
							flag = True
						elif d not in new_state:
							if d in nfa.final_states:
								final = True
							new_state += [d]
		if new_state != []:
			new_state_str = ""
			for st in new_state:
				new_state_str += str(st)
			if new_state_str != "":
				if flag == False:
					new_transition[(int(state_name), l)] = int(new_state_str)
				else:
					new_transition[(int(state_name), l)] = int(state_name)

	if new_transition == dict():
		return None
	return (new_transition, final)

def nfa_to_dfa(nfa):
	
	finished_states = list()

	start_state = nfa.start_state
	alphabet = nfa.alphabet
	delta = nfa.delta

	first_states = list()
	first_states.append(start_state)
	
	eps = None

	for t in delta:
		# t e de forma (stare, word) => un tuplu
		if t[1] == "" and t[0] == start_state:
			eps = delta[t]

	# inchiderile eps ale starii initiale
	if eps != None:
		for state in eps:
			first_states.append(state)

	for k in first_states:
		for t in delta:
			if t[0] == k and t[1] == "":
				dict_d = list(delta[t])
				for i in dict_d:
					if i not in first_states:
						first_states.append(i)

	start_stateDFA = ""
	# fac prima stare
	for s in first_states:
		start_stateDFA += str(s)

	all_statesDFA = set()
	all_statesDFA.add(int(start_stateDFA))
	final_statesDFA = set()
	transitionsDFA = dict()

	states_from_first_state = list()
	
	all_statesDFA.add(int(start_stateDFA))

	for f in first_states:
		if f in nfa.final_states:
			final_statesDFA.add(int(start_stateDFA))
			break
	for l in alphabet:
		new_state = list()
		for s in first_states:
			for t in delta:
				if t[0] == s and t[1] == l:
					if delta[t] not in new_state:
						new_state += list(delta[t])
						for i in delta[t]:
							for k in delta:
								if k[0] == i and k[1] == "":
									new_state += delta[k]
		if new_state != []:
			for st in new_state:
				for t in delta:
					if t[0] == st and t[1] == "":
						eps_close = delta[t]
						for i in  eps_close:
							if i not in new_state:
								new_state.append(i)
			states_from_first_state.append(new_state)
			new_state_str = ""
			for state in new_state:
				new_state_str += str(state)
			if new_state_str != "":
				all_statesDFA.add(int(new_state_str))
				for state in new_state:
					if state in nfa.final_states:
						final_statesDFA.add(int(new_state_str))
				transitionsDFA[(int(start_stateDFA), l)] = int(new_state_str)

	
	# states_from.. = lista de liste
	new_tranz = None
	next_states = list()
	
	state_with_flag = ""
	for state in states_from_first_state:

		state_name = ""
		for i in state:
			finished_states.append(i)
			state_name += str(i)
		tuple_tranz = get_transition(nfa, state)
		if tuple_tranz != None:
			new_tranz = tuple_tranz[0]
			is_final = tuple_tranz[1]
		if tuple_tranz != None:
			new_list = list()
			if next_states != []:
				for s in str(next_states):
					if int(s) not in finished_states:
						new_list.append(int(s))

			for v in new_tranz:
				all_statesDFA.add(new_tranz[v])
				digits = [int(x) for x in str(new_tranz[v])]
				for i in digits:
					if i in nfa.final_states or is_final == True:
						final_statesDFA.add(new_tranz[v])
			transitionsDFA = merge_dicts(transitionsDFA, new_tranz)

	dfa = DFA(alphabet, all_statesDFA, int(start_stateDFA), final_statesDFA, transitionsDFA)
	return dfa


	
if __name__ == "__main__":
    valid = (len(sys.argv) == 4 and sys.argv[1] in ["RAW", "TDA"]) or \
            (len(sys.argv) == 3 and sys.argv[1] == "PARSE")
    if not valid:
        sys.stderr.write(
            "Usage:\n"
            "\tpython3 main.py RAW <regex-str> <words-file>\n"
            "\tOR\n"
            "\tpython3 main.py TDA <tda-file> <words-file>\n"
            "\tOR\n"
            "\tpython3 main.py PARSE <regex-str>\n"
        )
        sys.exit(1)

    if sys.argv[1] == "TDA":
        tda_file = sys.argv[2]
        with open(tda_file, "rb") as fin:
            parsed_regex = pickle.loads(fin.read())
    else:
        regex_string = sys.argv[2]
        # TODO "regex_string" conține primul argument din linia de comanda,
        # șirul care reprezintă regexul cerut. Apelați funcția de parsare pe el
        # pentru a obține un obiect RegEx pe care să-l stocați în
        # "parsed_regex"
        #
        # Dacă nu doriți să implementați parsarea, puteți ignora această parte.
        parsed_regex = parseRegEx(regex_string)
        if sys.argv[1] == "PARSE":
            print(str(parsed_regex))
            sys.exit(0)

    # În acest punct, fie că a fost parsat, fie citit direct ca obiect, aveți
    # la dispoziție variabila "parsed_regex" care conține un obiect de tip
    # RegEx. Aduceți-l la forma de Automat Finit Determinist, pe care să puteți
    # rula în continuare.

    #conversa RegEx => ExpresieRegulata
   
    if str(parsed_regex) != ".":
    	
    	regular_expression = convertRegEx(parsed_regex)
	  
	    #conversia ExpresieRegulata => AFN
    	nfa = re_to_nfa(regular_expression)
	  
	    #conversia AFN => AFD
    	dfa = nfa_to_dfa(nfa)

    with open(sys.argv[3], "r") as fin:
        content = fin.readlines()


    for word in content:
        # TODO la fiecare iterație, "word" conținue un singur cuvânt din
        # fișierul de input; verificați apartenența acestuia la limbajul
        # regexului dat și scrieți rezultatul la stdout.
       
        if str(parsed_regex) == ".":
        	if len(word) == 2:
        		print("True")
       		else:
        		print("False")
        else:
        	next_state = dfa.start_state
	        for letter in word:
	        	if letter != "\n":
	        		ok = 0
		        	for t in dfa.delta:
		        		if t[1] == letter and t[0] == next_state:
		        			next_state = dfa.delta[t]
		        			ok = 1
		        	if ok == 0:
		        		next_state = -3
	        			
	        if next_state in dfa.final_states:
	        	print("True")
	        else:
	        	print("False")
        pass
