import sys
import os

currentdirectory = os.path.dirname(os.path.realpath(__file__))

sys.path.append(currentdirectory+"/packages/ply/")
sys.path.append(currentdirectory+"/packages/plyj/")
sys.path.append(currentdirectory+"/packages/pyparsing/")
sys.path.append(currentdirectory+"/packages/pycparser1/")
sys.path.append(currentdirectory+"/packages/pycparserext/")
#sys.path.append(currentdirectory+"/packages/regex/")
sys.path.append(currentdirectory+"/packages/mpmath/")
sys.path.append(currentdirectory+"/packages/sympy/")
sys.path.append(currentdirectory+"/packages/z3/python/")
from pyparsing import *
import copy
import regex
from sympy import *
from sympy.core.relational import Relational
from pycparser1 import parse_file,c_parser, c_ast, c_generator
from pycparserext.ext_c_parser import GnuCParser
from pycparserext.ext_c_generator import GnuCGenerator
from itertools import permutations
#import execnet
ParserElement.enablePackrat()

def is_empty(any_structure):
    if any_structure:
        return False
    else:
        return True

def is_number(s):
    if s=='j':
    	return False
    try:
        float(s) # for int, long and float
    except ValueError:
        try:
            complex(s) # for complex
        except ValueError:
            return False
    except TypeError:
            return False
    return True

def is_hex(input_string):
        flag=True
        if input_string is None:
            return None
        try:
            flag=int(input_string, 16)
        except ValueError:
            return None
        if flag:
            if '0x' in input_string:
                 return str(int(input_string, 16))
            else:
                 return None
        else:
    	     return None


#Find Intersection of Two lists


def intersect3(c1,c2,c3):
	return list(set(list(set(c1) & set(c2)))-set(c3))

def intersect2(c1,c2):
	return list(set(c1) & set(c2))
        
def merge_two_dicts(x,y):
    z=x.copy()
    z.update(y)
    return z


# base language (non dynamic, not changed by the program)
# do not use name with number in the end
# these names are not supposed to be used as prorgam variables

_base = ['=','==','!=','<','<=','>','>=','*','**','!','+','-','/', '%', 'ite', 'and', 'or', 'not', 'implies', 'all', 'some', 'null','>>','<<','&','|','^']
_infix_op = ['=','==','!=','<','<=','>','>=','*','**','+','-','/', '%', 'implies','<<','>>','&','|','^']
_relation_op = ['==','!=','<','<=','>','>=']

# variables introduced in the translation

def isvariable(x):
    if x.startswith('_x') or  x.startswith('_y') or  x.startswith('_n') or  x.startswith('_s'):
        return True
    else:
        return False



# program variables and temporary program variables and big N

def is_program_var(x,v):
    if x.startswith('_N'):
        return True
    for y in v:
        if x==y or x.startswith(y+OUT) or (x.startswith(y+TEMP) and 
                                           x[len(y+TEMP):].isdigit()) or x.startswith(y+LABEL):
            return True
    return False


current_milli_time = lambda: int(round(time.time() * 1000))

"""
#Get timestap
"""

def getTimeStamp():
	ts = time.time()
	st = datetime.datetime.fromtimestamp(ts).strftime('%Y-%m-%d %H:%M:%S')
	return "\n***********************\n"+str(st)+"\n***********************\n"


"""
RET for return value of a function
Temporary function names are constructed as: 
variable-name + TEMP + TC
Output function names are: 
variable-name + LABEL
for those with label, or
variable-name + OUT
for those without label.
 TC: TempCount, a global counter for naming temporary variables
 LC: LoopCount, a global counter for naming loop constants and variables
"""

RET='RET'
#OUT='Z' #so don't name variables xZ, yZ...
OUT='1' #so don't name variables x1, y1...
#TEMP = 'T' #so if x is a variable, then don't name variables xT, 
TEMP = '' #so if x is a variable, then don't name variables x2,x3,... (temp starts at 2)
LABEL = '_' #so if x is a variable, then don't name variables x_1,x_2, 
TC = 1  # for generating temporary functions to yield xt1,xt2,...
LC = 0  # for generating smallest macro constants in a loop _N1, _N2,... as well as
               # natural number variables _n1,_n2,...
"""
 Expressions: (f e1 ... ek) is represented as [f,e1,...,ek].
 Example: a+1 is ['+', ['a'],['1']]; constant a is ['a']; 
 sum(i+1,j) is ['sum', ['+', ['i'], ['1']], ['j']]
"""


#constructor: functor - a string like '+', '*', 'and', 
# or constants like '1', 'x'; args - a list of exprs
def expres(functor,args=[]):
    return [functor]+args

#accessor
def expr_op(e):
    return e[0]
def expr_args(e):
    return e[1:]

#prefix printing
def expr2string(e):
    if len(e)==1:
        return e[0]
    else:
        return '(' + e[0] +' '+ ' '.join(list(expr2string(x) for x in e[1:]))+ ')'

#normal infix printing
def expr2string1(e):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        return op
    else:
        if op=='and' or op=='or':
            if len(args)==1:
                return expr2string1(args[0])
            else:
                return '('+(' '+op+' ').join(list(expr2string1(x) for x in args))+')'
        elif op=='not' and len(args)==1:
            return 'not '+expr2string1(args[0])
        elif op=='implies' and len(args)==2:
            return expr2string1(args[0])+ ' -> '+expr2string1(args[1])
        elif op in _infix_op and len(args)==2:
            return '(' + expr2string1(args[0])+ op+expr2string1(args[1])+')'
        else:
            return op +'('+ ','.join(list(expr2string1(x) for x in args))+ ')'


#return the list of program variables in an expression 

def expr_func(e,v): #e - expr
    ret = []
    f = expr_op(e)
    if is_program_var(f,v) or '__VERIFIER_nondet' in f:
        ret.append(f)
    for e1 in expr_args(e):
        ret = ret + expr_func(e1,v)
    return ret
    

#substitution of functors: in e, replace functor n1 by n2
def expr_sub(e,n1,n2): # e - expr; n1,n2 - strings
    e1=list(expr_sub(x,n1,n2) for x in e[1:])
    if e[0]==n1:
        return [n2]+e1
    else:
        return e[:1]+e1
        

#substitution of functors in a set: in e, for all x in v1 but not in v2, replace x+n1 by x+n2
def expr_sub_set(e,n1,n2,v1,v2): #e - expr; n1,n2 - strings, v1, v2 - sets of strings
    e1 = list(expr_sub_set(e2,n1,n2,v1,v2) for e2 in e[1:])
    if e[0].endswith(n1):
        x = e[0][:len(e[0])-len(n1)]
        if (x in v1) and (not x in v2):
            return [x+n2]+e1
        else:
            return e[:1]+e1
    else:
        return e[:1]+e1
        
        

# expr_replace(e,e1,e2): replace all subterm e1 in e by e2

def expr_replace(e,e1,e2): #e,e1,e2: expr
    if e==e1:
        return e2
    else:
        return e[:1]+list(expr_replace(x,e1,e2) for x in expr_args(e))
        
        

# expr_sub_dict(e,d): d is a dictonary of substitutions: functor 'f' to e1=d['f'] so that in e, each f term f(t1,...,tk) is replaced by e1(_x1/t1,...,_xk/tk)

def expr_sub_dict(e,d):
    args = expr_args(e)
    args1 = list(expr_sub_dict(x,d) for x in args)
    if expr_op(e) in d:
        return expr_sub_var_list(d[expr_op(e)],list(expres('_x'+str(i+1)) for i in range(len(args))),args1)
    else:
        return expres(expr_op(e),args1)
        

# expr_sub_var_list(e,l1,l2): in e, replace all terms in l1 by the corresponding terms in l2

def expr_sub_var_list(e,l1,l2): #e: expr, l1,l2: lists of the same length of exprs
    for i,x in enumerate(l1):
        if e==x:
            return l2[i]
    return e[:1]+list(expr_sub_var_list(y,l1,l2) for y in expr_args(e))


# compute E[n] extend(e,n,excl,v). n is an expr like ['_n1'], excl is a container of strings that are not to be extended
def extend(e,n,excl,v):
    op = expr_op(e)
    x = [n] if (is_program_var(op,v) and not (op in excl)) or '__VERIFIER_nondet' in op else []
    return expres(op, list(extend(e1,n,excl,v) for e1 in expr_args(e)) + x)


#A dictionary of dependencies para is such that, if x is an input variable, then para[x] is a list whose first element is 1 and the second element is the variable's parameter name; otherwise, para[x] is the list of input variables that x is depended on. 
#example: para = { 'X':[1,['_y1']], 'X11':[0,['_y1','_y2'], ['X','Y']],...} meaning 'X' is an input variable parameterized as '_y1' and 'X11' is a function depending on X and Y whose corresponding parameters are '_y1' and '_y2', respectively.
#So after parameterization, X11(a,X) will become X11(a,_y1,_y1,_y2)

def parameterize_expres(e,para): 
    if e[0] in para:
        if para[e[0]][0] == 1:
            return para[e[0]][1]+list(parameterize_expres(x,para) for x in e[1:])
        else:
            return e[:1]+list(parameterize_expres(x,para) for x in e[1:])+para[e[0]][1]
    else:
        return e[:1]+list(parameterize_expres(x,para) for x in e[1:])


#parameterize non-input functions then restore the input variables to its name
#given above para, X11(a,X) will become X11(a,X,X,Y), assuming that _y2 corresponds to Y

def parameterize_expr_sub(e,para): 
    if e[0] in para:
        if para[e[0]][0] == 1:
            return [e[0]]+list(parameterize_expr_sub(x,para) for x in e[1:])
        else:
            return e[:1]+list(parameterize_expr_sub(x,para) for x in e[1:])+para[e[0]][2]
    else:
        return e[:1]+list(parameterize_expr_sub(x,para) for x in e[1:])




        


"""
 Formulas:
 1. equations f(x) = e: ['e',e1,e2], 
    where e1 is expression for f(x) and e2 for e
 2. inductive definition:
 - base case f(x1,...,xk,0,...,xm)=e: ['i0',k,e1,e2] 
   where e1 is Expr for f(x1,...,xk,0,...,xm) and e2 the Expr for e
 - inductive case f(x1,...,xk,n+1,...,xm)=e: ['i1',k,'n',e1,e2] 
    where e1 is Expr for f(x1,...,xk,n+1,...,xm) and e2 the Expr for e
 3. inductive definition for functions that return natural numbers 
    (like N in smallest macro):
 - base case f(x) = 0 iff C: ['d0',e,c] 
   where e is the Expr for f(x) and c an expression for condition C
 - inductive case f(x) = n+1 iff C(n): ['d1','n',e,c] 
   where e is the Expr for f(x) and c an Expr for condition C
 4. any other axioms: A: ['a',e], where e is the Expr for A
 5. constraints from smallest macro smallest(N,n,e):
    ['s0', e(N)] 
    ['s1', forall n<N -> not e]

 Examples: a' = a+1: ['e', ['a\''], ['+',['a'],['1']]]
 N(x) = 0 if x<I else N(x-1)+1 is divided into two axioms:
 N(x) = 0 iff x<I:  
 ['d0', ['N',['x']], ['<', ['x'],['I']]] and
 N(x) = n+1 iff n=N(x-1): 
 ['d1','n', ['N',['x']], ['=',['n'], ['N', ['-', ['x'],['1']]]]]
"""


# constructors
def wff_e(e1,e2): #e1,e2: expr
    return ['e',e1,e2]

def wff_i0(k,e1,e2): #k: int; e1,e2: expr
    return ['i0',k,e1,e2]

def wff_i1(k,v,e1,e2): #k: int; v: string; e1,e2: expr
    return ['i1',k,v,e1,e2]

def wff_d0(e,c): #e: expr; c: expr
    return ['d0',e,c]

def wff_d1(v,e,c): #v: string, e and c: expr
    return ['d1',v,e,c]

def wff_a(e): #e: expr
    return ['a',e]

def wff_s0(e):
    return ['s0',e]
def wff_s1(e):
    return ['s1',e]
    
def wff_c1(e):
    return ['c1',e]

    
    
#print in prefix notation
def wff2string(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1' or w[0] == 'R':
            return '(= '+expr2string(w[-2])+' '+expr2string(w[-1]) +')'
        elif w[0] == 'd0':
            return '(iff (= '+expr2string(w[1])+' 0) '+ expr2string(w[2])+')'
        elif w[0] == 'd1':
            return '(iff (= '+expr2string(w[2])+' (+ '+w[1]+' 1)) '+expr2string(w[3])+')'
        elif w[0]=='a' or w[0]=='s0' or w[0]=='s1' or w[0]=='c1' or w[0] == 'R':
            return expr2string(w[1])

#print in normal infix notation
def wff2string1(w):
        if w[0] == 'e' or w[0] == 'i0' or w[0] == 'i1' or w[0] == 'i2' or w[0] == 'R':
            return expr2string1(w[-2])+' = '+ expr2string1(w[-1])
        elif w[0] == 'd0':
            return expr2string1(w[1])+'=0 <=> '+ expr2string1(w[2])
        elif w[0] == 'd1':
            return expr2string1(w[2])+'='+w[1]+'+1 <=> '+expr2string1(w[3])
        elif w[0]=='a' or w[0]=='s0' or w[0]=='s1' or w[0]=='c1':
            return expr2string1(w[1])



#strip '(' at the beginning and matching ')' in the end of a string
def trim_p(s):
    if s.startswith('(') and s.endswith(')'):
        return trim_p(s[1:-1])
    else:
        return s


#print in normal infix notation
def wff2subslist(w):
        if w[0] == 'e':
            return expr2string1(w[-2]),expr2string1(w[-1])


#strip '(' at the beginning and matching ')' in the end of a string
def trim_p(s):
    if s.startswith('(') and s.endswith(')'):
        return trim_p(s[1:-1])
    else:
        return s



#for a formula w, compute w[n]
def wff_extend(w,n,excl,v): #w: wff, n: expr, excl: container of strings
    if w[0]=='e': #['e',e1,e2]
        return ['e',extend(w[1],n,excl,v),extend(w[2],n,excl,v)]
    elif w[0]=='i0': #['i0',k,e1,e2]
        return ['i0',w[1],extend(w[2],n,excl,v),extend(w[3],n,excl,v)]
    elif w[0]=='i1': #['i1',k,v,e1,e2]
        return ['i1',w[1],w[2],extend(w[3],n,excl,v),extend(w[4],n,excl,v)]
    elif w[0]=='d0': #['d0',e,c]
        return ['d0',extend(w[1],n,excl,v),extend(w[2],n,excl,v)]
    elif w[0]=='d1': #['d1',v,e,c]
        return ['d1',w[1],extend(w[2],n,excl,v),extend(w[3],n,excl,v)]
    elif w[0]=='a' or w[0]=='s0' or w[0]=='s1': 
        return [w[0], extend(w[1],n,excl,v)]
    else:
        print('Not a wff')
        return
        

#for a formula w, replace functor old by new
def wff_sub(w,old,new): #w - wff; old, new - string
    if w[0]=='e': #['e',e1,e2]
        return ['e',expr_sub(w[1],old,new),expr_sub(w[2],old,new)]
    elif w[0]=='i0': #['i0',k,e1,e2]
        return ['i0',w[1],expr_sub(w[2],old,new),expr_sub(w[3],old,new)]
    elif w[0]=='i1': #['i1',k,v,e1,e2]
        return ['i1',w[1],w[2],expr_sub(w[3],old,new),expr_sub(w[4],old,new)]
    elif w[0]=='d0': #['d0',e,c]
        return ['d0',expr_sub(w[1],old,new),expr_sub(w[2],old,new)]
    elif w[0]=='d1': #['d1',v,e,c]
        return ['d1',w[1],expr_sub(w[2],old,new),expr_sub(w[3],old,new)]
    elif w[0]=='a' or w[0]=='s0' or w[0]=='s1': #['a',e]
        return [w[0],expr_sub(w[1],old,new)]
    else:
        print('Not a wff')
        return
        

#for a formula w, replace functor x+old by x+new for those in v1 but not in v2
def wff_sub_set(w,old,new,v1,v2): #w - wff; old, new - string; v1,v2: sets
    if w[0]=='e': #['e',e1,e2]
        return ['e',expr_sub_set(w[1],old,new,v1,v2),expr_sub_set(w[2],old,new,v1,v2)]
    elif w[0]=='i0': #['i0',k,e1,e2]
        return ['i0',w[1],expr_sub_set(w[2],old,new,v1,v2),expr_sub_set(w[3],old,new,v1,v2)]
    elif w[0]=='i1': #['i1',k,v,e1,e2]
        return ['i1',w[1],w[2],expr_sub_set(w[3],old,new,v1,v2),expr_sub_set(w[4],old,new,v1,v2)]
    elif w[0]=='d0': #['d0',e,c]
        return ['d0',expr_sub_set(w[1],old,new,v1,v2),expr_sub_set(w[2],old,new,v1,v2)]
    elif w[0]=='d1': #['d1',v,e,c]
        return ['d1',w[1],expr_sub_set(w[2],old,new,v1,v2),expr_sub_set(w[3],old,new,v1,v2)]
    elif w[0]=='a' or w[0]=='s0' or w[0]=='s1': #['a',e]
        return [w[0],expr_sub_set(w[1],old,new,v1,v2)]
    else:
        print('Not a wff')
        return

#like expr_sub_dict(e,d) but on wffs

def wff_sub_dict(w,d): #w - wff; d - a dictionary as in expr_sub_dict(e,d)
    if w[0]=='e': #['e',e1,e2]
        return w[:2]+[expr_sub_dict(w[2],d)]
    elif w[0]=='i0': #['i0',k,e1,e2]
        return w[:3]+[expr_sub_dict(w[3],d)]
    elif w[0]=='i1': #['i1',k,v,e1,e2]
        return w[:4]+[expr_sub_dict(w[4],d)]
    elif w[0]=='d0': #['d0',e,c]
        return w[:2]+[expr_sub_dict(w[2],d)]
    elif w[0]=='d1': #['d1',v,e,c]
        return w[:3]+[expr_sub_dict(w[3],d)]
    elif w[0]=='a' or w[0]=='s0' or w[0]=='s1': #['a',e]
        return [w[0],expr_sub_dict(w[1],d)]
    else:
        print('Not a wff')
        return

#parameterize a set of axioms by making program functions as input variables
#para = { 'X':[1,['_y1']], 'X11':[0,['_y1','_y2'],['X','Y']],...} meaning 'X' is an input variable parameterized as '_y1' and 'X11' is a function taking two new parameters '_y1','_y2'
#X11(a,X)=X11(a+b,1) will become X11(a,_y1,_y1,_y2)=X11(a+b,1,_y1,_y2)
 
def parameterize_wff(ax,para):
    if not (ax[0] == 'a' or ax[0]=='s0' or ax[0]=='s1'):
        e1 = parameterize_expres(ax[-2],para)
        e2 = parameterize_expres(ax[-1],para)
        return ax[:-2]+[e1,e2]
    else:
        e2 = parameterize_expres(ax[-1],para)
        return [ax[0],e2]
        

#for all x in dep_set, add dep_set[x] as arguments, except when x is RET+OUT,
#replace it by foo()

def parameterize_axioms_fun(axioms,dep_set):
    for x in axioms:
        parameterize_wff_fun(x,dep_set)

def parameterize_wff_fun(ax,dep_set):
    if not (ax[0] == 'a' or ax[0]=='s0' or ax[0]=='s1'):
        e1 = parameterize_expres_fun(ax[-2],dep_set)
        e2 = parameterize_expres_fun(ax[-1],dep_set)
        return ax[:-2]+[e1,e2]
    else:
        e2 = parameterize_expres_fun(ax[-1],dep_set)
        return [ax[0],e2]

def parameterize_expres_fun(e,dep_set): 
    if e[0]==RET+OUT:
        if len(e) != 1:
            print('Something is wrong '+RET+OUT+' should not have arguments')
            return
        else:
            return dep_set[RET+OUT]
    elif e[0] in dep_set:
        return expres(e[0],list(parameterize_expres_fun(x,dep_set) for x in e[1:])+dep_set[e[0]])
    else:
        return expres(e[0],list(parameterize_expres_fun(x,dep_set) for x in e[1:]))
        
        
    

def eqset2string(d):
    for x in d:
        print(wff2string(d[x]))
def eqset2string1(d):
    for x in d:
        print(wff2string1(d[x]))

def eqset2string1Print(d):
    output_val=''
    for x in d:
        output_val+=wff2string1(d[x])+"\n"
    return output_val





# translate0(program,set of program variables) returns a dictionary of frame axioms, output equations, a list of other axioms and a label

def translate0(p,v,flag):
    if p[1]=='while':
        return translateWhile(p,v,flag)
    if p[1]=='seq':
        return translateSeq(p,v,flag)
    if p[1]=='if1':
        return translateIf1(p,v,flag)
    if p[1]=='if2':
        return translateIf2(p,v,flag)
    if p[1]=='=':
        return translateAssign(p,v,flag)
    if p[1]=='fun':
        return translateFun(p,v,flag)
    if p[1]=='prog':
        return translateProgram(p,v,flag)
     
     
# function definition
def translateFun(p,v,flag): #p=['-1','fun',['foo','x',..,'y'], b]
    #global TC
    #global LC
    #TC=0
    #LC=0
    f,o,a,l = translate0(p[-1],v,flag)
    axioms=a
    for x in f:
        axioms=axioms+[f[x]]
    for x in o:
        axioms=axioms+[o[x]]
    g = graph(axioms,v) #construct dependency graph
    param = list(expres(a) for a in p[-2][1:]) #parameters of the function
    dep_set = {} #dependency set for each variables in the axiom
    dep_set[RET+OUT]=expres(p[-2][0],param) #initialize it to the return function
    for (x,y) in g:
        if (not x in dep_set) and (not expres(x) in param):
            dep = []
            for x1 in reach_set([x],g):
                if (expres(x1) in param) and not (expres(x1) in dep):
                    dep.append(expres(x1))
            dep_set[x] = dep
    
    
    for x in f:
        f[x]=parameterize_wff_fun(f[x],dep_set)
    for x in o:
        o[x]=parameterize_wff_fun(o[x],dep_set)
    for i,ax in enumerate(a):
        a[i]=parameterize_wff_fun(ax,dep_set)
    return [dep_set[RET+OUT],f,o,a,l]
    
      
    
    
# program: a set of functions   
#p=['-1','prog',[f1,...,fk]] 
#for each fi, v[fi] is the list of variables used in the function fi
def translateProgram(p,v,flag): 
    result = {}
    for x in p[-1]:
        funcName = x[2][0]
        result[funcName] = translate0(x,v[funcName],flag)
    return result


# assignment translation: p a program and v a set of program variables

map___VERIFIER_nondet={}

def translateAssign(p,v,flag): #p=[l,'=',left,right]
    global map___VERIFIER_nondet
    if p[1] != '=':
        print('Not an assignment')
        return
    left = p[2] #left side of the assigment
    op = left[0] #the functor in left
    arity = len(left)-1 #arity of op
    right = p[3] #right side of the assignment
    right = update__VERIFIER_nondet_stmt(right,map___VERIFIER_nondet)
    out=OUT if p[0] == '-1' else LABEL+p[0]
    out_axioms = {}
    frame_axioms = {}
    for x in v:
        if x == op:
            args = list(expres('_x'+str(i+1)) for i in range(arity))
            cond = expres('=',[expres('_x1'),left[1]]) if arity==1 else \
                   expres('and', list(expres('=', [expres('_x'+str(i2+1)),y]) for \
                                    i2,y in zip(range(arity),left[1:])))
            if arity == 0:
                out_axioms[x]=wff_e(expres(op+out),right)
            else:
                out_axioms[x]=wff_e(expres(op+out,args), expres('ite',[cond,right,expres(op,args)]))
        else:
            args = list(expres('_x'+str(i+1)) for i in range(len(v[x])-2))
            frame_axioms[x]=wff_e(expres(x+out,args), expres(x,args))


    return frame_axioms, out_axioms, [], p[0]
    
    
    

def translateIf1(p,v,flag): # p=[l,'if1',c,e]
    global map___VERIFIER_nondet
    if p[1] != 'if1':
        print('Not an if-then')
        return
    global TC
    frame_axioms,out_axioms,axioms,llabel = translate0(p[3],v,flag)
    old_out = OUT if llabel=='-1' else LABEL+llabel
    out=OUT if p[0] == '-1' else LABEL+p[0]
    if llabel=='-1': # body has no final label
        TC += 1
    body_out = TEMP+str(TC) if llabel=='-1' else LABEL+llabel
    
    p[2] = update__VERIFIER_nondet_stmt(p[2],map___VERIFIER_nondet)
    
    for x in v:
        if x in frame_axioms: 
            ax = frame_axioms[x] #ax = ['e',e1,e2]
            if llabel != '-1': #body has label: keep axioms about it
                axioms.append(ax)
            #generate the new frame axiom
            frame_axioms[x] = wff_e(expr_sub(ax[1],x+old_out,x+out), ax[2])
        else:
            ax = out_axioms[x] #ax = ['e',e1,e2]
            if llabel != '-1': #body has label: keep axioms about it
                axioms.append(ax)
            out_axioms[x] = wff_e(expres(x+out, ax[1][1:]),
                                  expres('ite', [p[2], ax[2], expres(x,ax[1][1:])]))
    return frame_axioms, out_axioms, axioms, p[0]
    
            
def translateIf2(p,v,flag): # p=[l,'if2',c,e1,e2]
    global map___VERIFIER_nondet
    if p[1] != 'if2':
        print('Not an if-then-else')
        return
    global TC
    frame_axioms0,out_axioms0,axioms0,llabel0 = translate0(p[3],v,flag)
    frame_axioms1,out_axioms1,axioms1,llabel1 = translate0(p[4],v,flag)
    axioms = axioms0+axioms1
    old_out0 = OUT if llabel0=='-1' else LABEL+llabel0
    old_out1 = OUT if llabel1=='-1' else LABEL+llabel1
    out=OUT if p[0] == '-1' else LABEL+p[0]
    if llabel0=='-1': # if body has no final label
        TC += 1
    body_out0 = TEMP+str(TC) if llabel0=='-1' else LABEL+llabel0 # if body new out
    if llabel1=='-1': # else body has no final label
        TC += 1
    body_out1 = TEMP+str(TC) if llabel1=='-1' else LABEL+llabel1 # else body new out
    frame_axioms = {}
    out_axioms = {}
    
    p[2] = update__VERIFIER_nondet_stmt(p[2],map___VERIFIER_nondet)
    
    for x in v:
        if x in frame_axioms0 and x in frame_axioms1: 
            ax0 = frame_axioms0[x] #ax0 = ['e',e1,e2]
            ax1 = frame_axioms1[x] #ax1 = ['e',e1,e2]
            if llabel0 != '-1': #if body has label: keep axioms about it
                axioms.append(ax0)
            if llabel1 != '-1': #else body has label: keep axioms about it
                axioms.append(ax1)
            #generate the new frame axiom
            frame_axioms[x] = wff_e(expr_sub(ax0[1],x+old_out0,x+out), ax0[2])
        else:
            if x in frame_axioms0:
                ax0=frame_axioms0[x]
            else:
                ax0=out_axioms0[x]
            if x in frame_axioms1:
                ax1=frame_axioms1[x]
            else:
                ax1=out_axioms1[x]
            if llabel0 != '-1': #if body has label: keep axioms about it
                axioms.append(ax0)
            if llabel1 != '-1': #else body has label: keep axioms about it
                axioms.append(ax1)
            out_axioms[x] = wff_e(expres(x+out, ax0[1][1:]),
                                  expres('ite', [p[2], ax0[2], ax1[2]]))
    return frame_axioms, out_axioms, axioms, p[0]
    
            
def translateSeq(p,v,flag): # p=['-1','seq',p1,p2]
    if p[1] != 'seq':
        print('Not a sequence')
        return
    global TC
    frame_axioms0,out_axioms0,axioms0,llabel0 = translate0(p[2],v,flag)
    frame_axioms1,out_axioms1,axioms1,llabel1 = translate0(p[3],v,flag)
    old_out0 = OUT if llabel0=='-1' else LABEL+llabel0
    if llabel0=='-1': # if p1 has no final label
        TC += 1
    new_out0 = TEMP+str(TC) if llabel0=='-1' else LABEL+llabel0 # p1 new out
    frame_axioms = {}
    out_axioms = {}
    para = {} #a dictonary of substitution: para[x] is the expression to replace x(t) in p2's axioms
    for x in v:
        if x in frame_axioms0 and x in frame_axioms1:
            if llabel0 !='-1': #p1 has label, keep its axioms
                axioms0.append(frame_axioms0[x])
            frame_axioms[x]=frame_axioms1[x]
        else:
            if x in frame_axioms0:
                ax0=frame_axioms0[x] #ax0=['e',e1,e2]
            else:
                ax0=out_axioms0[x]
            if llabel0 != '-1': #p1 has label: keep equations about it
                axioms0.append(ax0)
            para[x]=ax0[2]
    for i,ax in enumerate(axioms1): #substituting p1's output into p2's input in p2's axioms
        axioms1[i] = wff_sub_dict(ax,para)
    for x in v: #do the same for the p2's output equations and frame axioms
        if not x in frame_axioms:
            if x in frame_axioms1:
                out_axioms[x] = frame_axioms1[x][:2]+[expr_sub_dict(frame_axioms1[x][2],para)]
            else:
                out_axioms[x] = out_axioms1[x][:2]+[expr_sub_dict(out_axioms1[x][2],para)]

    for x in out_axioms:

        out_axioms[x][-1] = simplification_expr(out_axioms[x][-1])


 
    for x in axioms0:
        x[-1] = simplification_expr(x[-1])


    for x in axioms1:
        x[-1] = simplification_expr(x[-1])


    
    return frame_axioms, out_axioms, axioms0+axioms1, llabel1
    


def translateWhile(p,v,flag): #p=[l, 'while', c, b]
    global map___VERIFIER_nondet
    if p[1] != 'while':
        print('Not a while statement')
        return
    global LC
    global TC
    frame_axioms, out_axioms0, axioms,llabel = translate0(p[3],v,flag) # axioms and output labels for the body of the loop
    LC += 1
    if llabel=='-1': # if body has no final label
        if TC==0:
            TC += 2
        else:
            TC += 1
        
    loop_var = expres('_n'+str(LC)) #a new natural number variable for the loop
    smallest = expres('_N'+str(LC)) #a new natural number variable for the loop
    init=TEMP+str(TC) if llabel=='-1' else LABEL+llabel #iterating functions
    old_out=OUT if llabel=='-1' else LABEL+llabel #original output functions in body
    out=OUT if p[0]=='-1' else LABEL+p[0] #new output functions for the loop

    for i0, ax0 in enumerate(axioms): #extend the axioms with [n]
        ax0 = wff_sub_set(ax0,'',init,v,frame_axioms)
        axioms[i0]=wff_extend(ax0, loop_var, frame_axioms,v)

    for x in frame_axioms:
        ax = frame_axioms[x] #ax = ['e',e1,e2]
        if llabel != '-1': #body has label: keep axioms about it
            axioms.append(ax)
        #generate the new frame axiom
        frame_axioms[x] = wff_e(expr_sub(ax[1],x+old_out,x+out), ax[2])
    out_axioms00={}
    for x in out_axioms0: 
        ax = out_axioms0[x] #ax = ['e',e1,e2]
        #change output and input variable names to loop and extend e2[loop_var]
        ax = wff_sub_set(ax,old_out,init,v,frame_axioms)
        ax = wff_sub_set(ax,'',init,v,frame_axioms)
        out_axioms00[x]=ax[:2]+[extend(ax[2],loop_var,frame_axioms,v)]

    # using Pritom's solve_rec() to try to get closed-form solution
    found_solution=True
    variable=None
    temp_out_axioms00 = copy.deepcopy(out_axioms00)
    while found_solution:
        found1=False
        for x in temp_out_axioms00.keys():
            if x in out_axioms00.keys():
               ax=out_axioms00[x]
               if expr_func(ax[2],v)==[]:
                  found1=True
                  e=extend(ax[1],loop_var,frame_axioms,v)
                  axioms.append(wff_e(e,ax[2]))
                  del out_axioms00[x]
                  for y in out_axioms00:
                      ax1= out_axioms00[y]
                      out_axioms00[y]=ax1[:2]+[expr_sub_dict(ax1[2],{expr_op(ax[1]):ax[2]})]
               else:
                  e1=wff_i1(0,expr_op(loop_var),extend(ax[1],expres('+',[loop_var,['1']]),frame_axioms,v),ax[2])
                  e2=wff_i0(0,extend(ax[1],expres('0'),frame_axioms,v),expres(x,expr_args(ax[1])))
                  res=solve_rec(e1,e2)
                  if res != None: #res = ['i2',k,n,e1,e2]
                     found1=True
                     variable=res[2] # Variable add by Pritom Rajkhowa
                     axioms.append(wff_e(res[3],res[4]))
                     del out_axioms00[x]
                     for y in out_axioms00:
                         ax1= out_axioms00[y]
                         out_axioms00[y]=ax1[:2]+[expr_sub_dict(ax1[2],{expr_op(res[3]):res[4]})]
        if not found1:
            found_solution=False
    for x in out_axioms00:
        ax = out_axioms00[x] #ax = ['e',e1,e2]
        e1=extend(ax[1],expres('+',[loop_var,['1']]),frame_axioms,v)
        e2=ax[2]
        axioms.append(wff_i1(len(expr_args(e1))-1,expr_op(loop_var),e1,e2))
    
    #base case
    for x in out_axioms00:
        arity = len(v[x])-2
        args = list(expres('_x'+str(i+1)) for i in range(arity))
        axioms.append(wff_i0(arity,expres(x+init,args+[expres('0')]), expres(x,args)))
    c=p[2] #loop condition
    c = update__VERIFIER_nondet_stmt(c,map___VERIFIER_nondet)
    c=expr_sub_set(c,'',init,v,frame_axioms)
    c = extend(c,loop_var,frame_axioms,v) #add the smallest macro
     #Add by pritom
    cc = copy.deepcopy(c)
    axioms.append(wff_s0(expr_sub(expr_complement(cc),expr_op(loop_var),expr_op(smallest))))  
    #axioms.append(wff_s0(expres('not',[expr_sub(c,expr_op(loop_var),expr_op(smallest))])))
    axioms.append(wff_s1(expres('implies',
                             [expres('<', [loop_var, smallest]),c])))
    out_axioms = {}
    for x in v: # generate out_axioms
        if not x in frame_axioms:
            args = list(expres('_x'+str(i+1)) for i in range(len(v[x])-2))
            e1=expres(x+out,args)
            args.append(smallest)
            e2=expres(x+init,args)
            out_axioms[x]=wff_e(e1,e2)
    #substitution of closed form solution by pritom rajkhowa
    constant='_N'+str(LC)
    variable='_n'+str(LC)
    update_axioms=[]
    equations=[]

    for ax in axioms:
    	if ax[0]=='e':
    		equations.append(ax)
    	else:
    		update_axioms.append(ax)
    
    for equation in equations:
    	equation1=copy.deepcopy(equation)
    	update_axioms=solnsubstitution(update_axioms,equation[1],equation[2])
    	equation1[1]=expr_replace_const(equation1[1],variable,constant)
    	equation1[2]=expr_replace_const(equation1[2],variable,constant)
    	update_axioms=solnsubstitution(update_axioms,equation1[1],equation1[2])
    	for x in out_axioms:
            stmt=out_axioms[x]
            stmt[2]=expr_replace(stmt[2],equation1[1],equation1[2])
    axioms=update_axioms
    updated_axioms=[]
    for ax in axioms:
        if ax[0]=='s0':
           expression=expr2string1(ax[1])
           if '->' not in expression and constant in expression:
              if '**' not in expression:
                 #expression=normal_form_constant(expression, constant)
                 if '**' not in str(expression):
                     parser = c_parser.CParser()
                     ast = parser.parse("void test(){"+str(expression)+";}")
                     statement_temp=ast.ext[0].body.block_items[0]
                     axupdate = construct_expression_normalC(eval(expressionCreator_C(statement_temp)))
                     #axupdate=construct_expression_normal(tree)
                     if axupdate is not None:
                        updated_axioms.append(axupdate)
                     else:
                       updated_axioms.append(ax)
                 else:
                   updated_axioms.append(ax)
              else:
                updated_axioms.append(ax)
           elif '<=' in expression and 'and' not in expression and 'or' not in expression:
              if '**' not in expression:
                  #expression=normal_form_constant(expression, constant)
                  #expression = normal_form_constant(expression,  constant)
                  #pp = getParser()
                  if '**' not in str(expression):
                      if '**' not in str(expression):
                          parser = c_parser.CParser()
                          ast = parser.parse("void test(){"+str(expression)+";}")
                          statement_temp=ast.ext[0].body.block_items[0]
                          #tree = pp.parse_expression(str(expression))		 
                          #axupdate=construct_expression_normal(tree)
                          axupdate = construct_expression_normalC(eval(expressionCreator_C(statement_temp)))
                          if axupdate is not None:
                             updated_axioms.append(axupdate)
                          else:
                             updated_axioms.append(ax)
                  else:
                     updated_axioms.append(ax)
              else:
                  updated_axioms.append(ax)

           else:
              updated_axioms.append(ax)
        else:
           updated_axioms.append(ax)
    #------------------------------------------
    axioms=[]
    for ax in updated_axioms:
    	axioms.append(ax)

    #substitution of closed form solution by pritom rajkhowa  
    if flag==2:
        g = graph(axioms,v) #construct dependency graph
        for x in expr_func(p[2],v):
            if not ['_N'+str(LC), x] in g:
                g.append(['_N'+str(LC), x])
                g.append(['_N'+str(LC), x+init])
        for x in out_axioms00:
            if not [x+init,x] in g:
                g.append([x+init,x])
            if not [x,x+init] in g:
                g.append([x,x+init])
            for y in expr_func(out_axioms00[x][2],v):
                if not [x,y] in g:
                    g.append([x,y])
        #build a dictionary para = { 'X':[1,['_y1']], 'X11':[0,['_y1','_y2'],['X','Y'],...} 
        #meaning 'X' is an input variable parameterized as '_y1' and 
        #'X11' is a function taking two new parameters '_y1' and '_y2' which correspond 
        # to 'X' and 'Y', respectively
        para={} 
        for [x,x1] in g: #compute the dependency sets
            if x in v and not x in frame_axioms:
                para[x] = [1,[v[x][0]]]
            else:
                if not x in para and not x in frame_axioms:
                    t=[]
                    t1=[]
                    for y in reach_set([x],g):
                        if y in v and (not expres(y) in t1) and (not y in frame_axioms):
                            t.append(expres(v[y][0]))
                            t1.append(expres(y))
                    if t != []:
                        para[x] = [0,t,t1]
        #parameterize input variables that N depends on and all associated functions
        for i,ax in enumerate(axioms):
            axioms[i] = parameterize_wff(ax,para)
        #construct inductive definition for N
        s_args = para['_N'+str(LC)][1]
        smallest1=expres('_N'+str(LC), s_args)
        next_args=[]
        for i,y in enumerate(s_args):
            x=expr_op(para['_N'+str(LC)][2][i])
            next_args.append(parameterize_expres(out_axioms0[x][2],para))
        axioms.append(['d0',smallest1, parameterize_expres(expres('not',[p[2]]),para)])
        axioms.append(['d1','_n'+str(LC), smallest1, 
                       expres('=',[loop_var,expres('_N'+str(LC),next_args)])])
        #parameterize output axioms
        for x in out_axioms:
            out_axioms[x]=out_axioms[x][:2]+[parameterize_expr_sub(out_axioms[x][2],para)]
        new_axioms = [] #for creating new inductive definitions
        for ax in axioms:
            if ax[0]=='i1':
                x=expr_op(ax[3])
                if x.endswith(init) and x[:len(x)-len(init)] in v:
                    next_args=[]
                    for k,arg in enumerate(expr_args(ax[3])):
                        if k==ax[1]:
                            next_args.append(expres(ax[2]))
                        else:
                            a=expr_op(arg)
                            if a.startswith('_y'):
                                for b in v:
                                    if v[b][0]==a:
                                        next_args.append(parameterize_expres(out_axioms0[b][2],para))
                            else:
                                next_args.append(arg)
                    new_axioms.append(ax[0:4]+[expres(x,next_args)])
        axioms=axioms+new_axioms

    return frame_axioms, out_axioms, axioms, p[0]






#construct a graph of dependency relation in a set of equations axioms 
def graph(axioms,v):
    ret = []
    for ax in axioms:
        if ax[0]=='e' or ax[0]=='i0' or ax[0]=='i1' or ax[0]=='d0' or ax[0]=='d1':
            op=expr_op(ax[-2])
            for x in expr_func(ax[-1],v):
                if not [op,x] in ret:
                    ret.append([op,x])
        elif ax[0]=='s1':
            op=expr_op(expr_args(expr_args(ax[1])[0])[1])
            for x in expr_func(expr_args(ax[1])[1],v):
                if not [op,x] in ret:
                    ret.append([op,x])
    return ret

#given a list s of nodes, return the list of nodes that are reachable from the nodes in s
def reach_set(s,g):
    s1=[]
    for [n1,n2] in g:
        if (n1 in s) and not (n2 in s):
            s1.append(n2)
    if s1==[]:
        return s
    else:
        return reach_set(s+s1,g)

                            
# testing examples. 
x=expres('x')
y=expres('y')
ex1 = ['-1','=',x, expres('+',[y,['1']])] #x=y+1
ex2 = ['-1','=',y, ['+',y,['1']]] #y=y+1
ex21 = ['1','=',y, ['+',y,['1']]] #1: y=y+1
ex22 = ['-1','if1',['>', y,['1']],ex2] # if y>1 then y=y+1
ex23 = ['-1','if1',['>', y,['1']],ex21] # if y>1 then l: y=y+1
ex24 = ['-1','if2',['>', y,['1']],ex21,ex1] # if y>1 then l: y=y+1 else x=y+1
ex3 = ['-1','seq',ex1,ex2]  #x=y+1; y=y+1
v1 = {'x':['_y1','int'], 'y':['_y2','int']}
ex4 = ['-1', '=', ['t',x], ['+', ['+', ['z', x, ['t', x]], ['1']], x]]
ex42 = ['-1', '=', ['z',x,y], ['+', ['+', ['z', x, ['t', x]], ['1']], x]]
v2 = {'x':['_y1','int'], 'y':['_y2','int'], 't':['_y3','int','int'], 'z':['_y4','int','int','int']}
ex41 = ['-1','if1',['>', y,['1']],ex4] # if y>1 then ex4

ex25 = ['-1','if2',['>', y,['1']],ex1,ex4] 

ex5 = ['-1','if2',expres('and', [expres('=', [expres('x'),expres('t',[expres('1')])]), expres('<', [expres('y'), expres('z',[expres('x'),expres('y')])])]), ex1, ex4]

ex6 = ['-1','while',expres('<',[expres('x'),expres('y')]),ex4]

#translate1(ex3,v1,1)
#translate1(ex4,v2,1)
#translate1(ex5,v2,1)

# factorial function
"""
i=1;
F=1;
while(i <= X) {
 F=F*i;
 i=i+1;
}
"""
i=expres('i')
F=expres('F')
X=expres('X')
fact0 = ['-1','seq',['-1','=',i,['1']],['-1','=',F,['1']]]
fact1 = ['-1','seq',['-1','=',F,['*',F,i]],['-1','=',i,['+',i,['1']]]]
fact2 = ['-1','while', ['<=',i,X], fact1]
fact = ['-1','seq',fact0,fact2]
vfact = {'i':['_y1','int'], 'X':['_y2','int'], 'F':['_y3','int'],RET:['_y0','int']}
#translate1(fact,vfact)

#factorial as a function: return F
fact3 = ['-1','=',expres(RET),F]
funfact = ['-1','fun',['factorial', 'X'],['-1','seq',fact,fact3]]
#a main() that uses factorial
# main1() { X=factorial(2) }
main1 = ['-1','fun',['main1'],['-1','=',X,expres('factorial',[expres('2')])]]
# variable list for main1()
man1v = {'X':['_y1','int']}
# variable lists for main1p, one for each function
main1pv = {'main1':man1v,'factorial':vfact}
main1p = ['-1','prog',[funfact,main1]]
# translate1(main1p, main1pv,1)

# in-place list reversing - see Lin and Yang 2015
"""
J = null;
while I != null do {
    K = next(I);
    next(I) = J;
    J=I;
    I=K;
}
I=J;
"""

lr6 = ['-1','=',['I'],['K']]
lr5 = ['-1','seq',['-1','=',['J'],['I']], lr6]
lr4 = ['-1','seq',['-1','=', ['next', ['I']],['J']], lr5]
lr3 = ['-1','seq',['-1','=',['K'],['next',['I']]], lr4]
lr2 = ['-1','while',['!=', ['I'], ['null']], lr3]
lr1 = ['-1','seq',lr2,['-1','=',['I'],['J']]]
lr = ['-1','seq',['-1','=',['J'],['null']], lr1]
vlr = {'J':['_y1','list'],'I':['_y2','list'],'K':['_y3','list'],'next':['_y4','list','list']}

#Cohen's division algorithm
"""
//XandYaretwoinputintegers;Y>0 
Q=0; // quotient
R=X; // remainder
while (R >= Y) do {
    A=1; // A and B are some that at any time for
    B=Y; // some n, A=2^n and B=2^n*Y
    while (R >= 2*B) do {
       A = 2*A;
       B = 2*B; }
    R = R-B;
    Q = Q+A }
//
return Q = X/Y;
"""

A=expres('A')
B=expres('B')
R=expres('R')
Q=expres('Q')
Y=expres('Y')
A2=expres('*',[expres('2'),A]) #2*A
B2=expres('*',[expres('2'),B]) #2*B
RB=expres('-',[R,B]) #R-B
QA=expres('+',[Q,A]) #Q+A
c1=expres('>=',[R,B2]) #R>=2*B
c2=expres('>=',[R,Y]) #R >= Y

cohen9=['-1','seq',['-1','=',A,A2],['-1','=',B,B2]]
cohen8=['-1','seq',['-1','=',R,RB],['-1','=',Q,QA]]
cohen7=['-1','while',c1, cohen9]
cohen6=['-1','seq',cohen7,cohen8]
cohen1=['-1','=',Q,['0']]
cohen5=['-1','seq',['-1','=',B,Y],cohen6]
cohen4=['-1','seq',['-1','=',A,['1']],cohen5]
cohen3=['-1','while',c2, cohen4]
cohen2=['-1','seq',['-1','=',R,X],cohen3]
cohen = ['-1', 'seq', cohen1,cohen2]
vcohen={'X':['_y1','int'],'Y':['_y2','int'],'Q':['_y3','int'],'R':['_y4','int'],'A':['_y5','int'],'B':['_y6','int']}

#product of two integers
"""
Z = 0;
while( Y!=0 ) {
 if ( Y % 2 ==1 ) {
     Z = Z+X;
     Y =(Y-1);
  }
  X = 2*X;
  Y = Y/2;
}
"""
Z=expres('Z')
prod1=['-1','seq',['-1','=',Z,expres('+',[Z,X])],['-1','=',Y,expres('-',[Y,['1']])]]
prod2=['-1','seq',['-1','=',X,expres('*',[['2'],X])],['-1','=',Y,expres('/',[Y,['2']])]]
prod3=['-1', 'if1', expres('=',[expres('%',[Y,['2']]), ['1']]), prod1]
prod4=['-1','seq',prod3,prod2]
prod5=['-1','while',expres('!=',[Y,['0']]),prod4]
prod = ['-1','seq',['-1','=',Z,['0']],prod5]
vprod = {'X':['_y1','int'],'Y':['_y2','int'],'Z':['_y3','int']}

#array sum array represented as a reference, and element represented by at predicate
"""
i=0;
sum=0;
while (i<size(A)) {
 sum=at(A,i)+sum
 i=i+1
}
"""
sum3=['-1','while',expres('<',[i,expres('size',[A])]),['-1','seq',['-1','=',['sum'],expres('+',[expres('at',[A,i]),['sum']])],['-1','=',i,expres('+',[i,['1']])]]]
sum2=['-1','seq',['-1','=',['sum'],['0']],sum3]
sum1=['-1','seq',['-1','=',i,['0']],sum2]
vsum = {'i':['_y1','int'],'sum':['_y2','int'],'size':['_y3','array','int'],'A':['_y4','array'],'at':['_y5','array','int','int']}

#Dijkstra's LCM algorithm
"""
X=A;  Y=B;  U=B;  V=A;
while (X!=Y) { 
  if (X>Y) {X=X-Y; V=V+U;} 
      else {Y=Y-X; U=U+V;}
}
"""

A=expres('A')
B=expres('B')
X=expres('X')
V=expres('V')
U=expres('U')
XY=expres('-',[X,Y])
YX=expres('-',[Y,X])
UV=expres('+',[U,V])
lcm1=['-1','seq',['-1','=',X,A],['-1','=',Y,B]]
lcm2=['-1','seq',lcm1,['-1','=',U,B]]
lcm3=['-1','seq',lcm2,['-1','=',V,A]]
lcm4=['-1','seq',['-1','=',X,XY],['-1','=',V,UV]]
lcm5=['-1','seq',['-1','=',Y,YX],['-1','=',U,UV]]
c1=expres('>',[X,Y])
lcm6=['-1', 'if2', c1, lcm4,lcm5]
c2=expres('!=',[X,Y])
lcm7=['-1','while',c2,lcm6]
lcm = ['-1','seq',lcm3,lcm7]
vlcm={'A':['_y1','int'],'B':['_y2','int'],'X':['_y3','int'],'Y':['_y4','int'],'U':['_y5','int'],'V':['_y6','int']}

"""
matrix multiplication from verifythis-2016 competition

int[][] matrixMultiply(int[][] A, int[][] B) {
	int n = A.length;

	// initialise C
	int[][] C = new int[n][n];

	for (int i = 0; i < n; i++) {
   		for (int k = 0; k < n; k++) {
       			for (int j = 0; j < n; j++) {
           			C[i][j] += A[i][k] * B[k][j];
       			}
   		}
	}
	return C;
 }
"""
def less(x,y):
    return expres('<',[x,y])
def passign(l,le,ri):
    return [l,'=',le,ri]
def initialize_array2(x,i,j,m,n):
    a=passign('-1',expres('d2array',[x,i,j]),expres('0')) #d2array(x,i,j)=0
    a1=passign('-1',i,expres('+',[i,expres('1')])) #i++
    a2=passign('-1',j,expres('+',[j,expres('1')])) #j++
    while1 = ['-1','while', less(j,n), ['-1','seq',a,a2]]
    body1 = ['-1','seq',while1,a1]
    body2 = ['-1','seq',passign('-1',j,expres('0')),body1]
    while2 = ['-1','while', less(i,m), body2]
    return ['-1','seq',passign('-1',i,expres('0')),while2]

mM1 = ['-1','seq',passign('-1',expres('n'),expres('length',[expres('a')])),
       initialize_array2(expres('c'),expres('i'),expres('j'),expres('n'),expres('n'))]
mM = ['-1','seq',mM1,passign('-1',expres(RET),expres('c'))]
# for now matrixMuliply only initializes C
matrixMultipy = ['-1','fun', ['matrixMultiply','a','b'],mM]
mMv = {'a':['_y1','array'],'b':['_y2','array'],'c':['_y3','array'],RET:['_y0','array'],'i':['_y4','int'],'j':['_y5','int'],'k':['_y6','int'],'n':['_y7','int'],'d2array':['_y7','array','int','int','int']}

# translate1(matrixMultipy,mMv,1)

"""
 A program variable has the attributes: its name, its type, 
 and its corresponding logical variable when parameterized. 
 A set of program variables is represented by a dictionary 
 with variable names as keys.
 examples: { 'X':['_y1','init','int','char'], 'I':['_y2','int'] }
 This set contains two program variables: 
 constant I of int value and function X from int*int to char
 Notice that the arity of a variable x in a set d is len(d[x])-2
 We assume no local function definitions, so the p in 'if b then p else p'
 'while b do p', 'foo(x,...,y) {b}' is a normal body of program statements.

 Program representations:
1. an assignment (l is the label, l='-1' means no label)
 l: left = right
 by [l,'=',e1,e2], 
 where e1,e2 are expressions representing left and right, respectively
2. a sequence
 p1; p2
 by ['-1','seq',p1,p2]
 where p1 and p2 are programs
3. if-then:
 l: if C then P
by [l,'if1', c,p], where c is the expression for C and p a program for P
4. if-then-else
 l: if c then p1 else p2
by [l,'if2', c,p1,p2], 
where c is Expr, p1 and p2 are Prog
5. while loop
 l: while c {b} by
[l,'while', c,b], 
where c is Expr, b is Prog
6. function definition
 foo(x,...,y) { B }
['-1','fun',['foo','x',..,'y'], b]
where 'foo' is the name of the function, 'x',...,'y' parameters, and
b the Prog representing B. We assume that B has no local function, i.e.
a normal body of statements. 
We assume a unique string 'RET' representing return
value because we do not have a special return statement.
Instead, a return statement
 l: return E
is represented as a normal assignment
 l: RET = e
We expect this will be the last statement of the body b
7. sequence of functions
 foo1(...) {B1}, ..., fook(...) {Bk}
['-1', 'prog', [f1,...,fk]]
where fi is the program representation of fooi(...) {Bi}. For this, the list
of variables v needs to be a dictionary indexed by the function names 
'foo1',...,'fook' whose value v['foo'] is the list of variables used in the function

"""



# for testing flag=1 (original translation), flag=2 (inductive definition for smallest N)
def translate1(p,v,flag):
    global TC
    global LC
    TC=0
    LC=0
    if p[1]=='prog':
        f_map={}
        a_map={}
        o_map={}
        cm_map={}
        assert_list_map={}
        assume_list_map={}
        assert_key_map={}
        res = translate0(p,v,flag)
        for fn in res:
            x,f,o,a,l = res[fn]
            #print f
	    #print o
            #print('Output for '+fn+':')
            
            simply_output_axioms_fn(f,o,a)
            
            f,o,a,cm = rec_solver(f,o,a)
            #f,o,a,cm = rec_solver_moment(f,o,a)
            #cm=[]          
            #print f
            #print o
            #print a

            
            organizeFreeVariable(f,o,a,v)
            
            #f,o,a,cm = getDummyFunction(f,o,a,cm)
            #f,o,a,cm = update__VERIFIER_nondet(f,o,a,cm)
            
            f,o,a,assert_list,assume_list,assert_key=getAssertAssume(f,o,a,cm)

            #f,o,a,assert_list,assume_list,assert_key=getAssertAssume(f,o,a,cm)
            
            
            #assert_list=[]
            
            #assume_list=[]
            
            #assert_key=[]
            
            assert_key_map={}
            
            
            f_map[fn]=f
            o_map[fn]=o
            a_map[fn]=a
            cm_map[fn]=cm
            
            assert_list_map[fn]=assert_list
            assume_list_map[fn]=assume_list
            assert_key_map[fn]=assert_key
            
            f,o,a=organizeOutput(f,o,a,v)
            
            
            f_map[fn]=f

            o_map[fn]=o

            a_map[fn]=a

            cm_map[fn]=cm

            output_val=''

            #output_axioms_fn(f,o,a)
 
            output_val+=output_axioms_fn_print(f,o,a)

            output_val+='\n4. Assumption :\n'
            for x in assume_list:

                if x[0]=='i1':

                        output_val+='\nForAll '+x[2]+' ( '+ expr2string1(x[-1])+' ) \n'


                else:

                        if x[0]=='e':

                               output_val+='\n'+expr2string1(x[-1])+'\n'

                        elif x[0]!='i0':

                               output_val+='\n'+wff2string1(x)+'\n'

            output_val+='\n5. Assertion :\n'
            for x in assert_list:

                if x[0]=='i1':

                        output_val+='\nForAll '+x[2]+' ( '+ expr2string1(x[-1])+' ) \n'


                else:

                        if x[0]=='e':

                               output_val+='\n'+expr2string1(x[-1])+'\n'

                        elif x[0]!='i0':

                               output_val+='\n'+wff2string1(x)+'\n'


        return f_map,o_map,a_map,cm_map,assert_list_map,assume_list_map,assert_key_map,output_val
        
    elif p[1]=='fun':
        fn,f,o,a,l = translate0(p,v,flag)
        print('Output for ')
        f,o,a,cm = rec_solver(f,o,a)
        #f,o,a,cm = getDummyFunction(f,o,a,cm)
        f,o,a,assert_list,assume_list,assert_key=getAssertAssume(f,o,a,cm)
        f,o,a=organizeOutput(f,o,a,v)
        output_val=''
        output_val+=output_axioms_fn_print(f,o,a)
        output_val+='\n4. Assumption :\n'
        for x in assume_list:
                if x[0]=='i1':
                       output_val+='ForAll '+x[2]+' ( '+ expr2string1(x[4])+' ) \n'
                else:
                        if x[0]!='i0':
                            output_val+=wff2string1(x)+"\n"
        output_val+='\n5. Assertion :\n'
        for x in assert_list:
               if x[0]=='i1':
                     output_val+='ForAll '+x[2]+' ( '+ expr2string1(x[4]) +' ) \n'
               else:
                     if x[0]!='i0':
                        output_val+=wff2string1(x)+"\n"
        return f,o,a,cm,assert_list,assume_list,assert_key,output_val
    else:
        f,o,a,l = translate0(p,v,flag)
        #Add by Pritom Rajkhowa 10 June 2016
        f,o,a,cm = rec_solver(f,o,a)
        #f,o,a,cm = getDummyFunction(f,o,a,cm)
        f,o,a,assert_list,assume_list,assert_key=getAssertAssume(f,o,a,cm)
        f,o,a=organizeOutput(f,o,a,v)
        output_axioms_fn(f,o,a)
        print('\n4. Assumption :')
        for x in assume_list:
	         if x[0]=='i1':
	         	print('ForAll '+x[2]+' ( '+ expr2string1(x[4])+' ) ')
	         else:
	                if x[0]!='i0':
                    		print(wff2string1(x))
        print('\n5. Assertion :')
        for x in assert_list:
               if x[0]=='i1':
                        print('ForAll '+x[2]+' ( '+ expr2string1(x[4])+' ) ')
               else:
                	if x[0]!='i0':
                    		print(wff2string1(x))
    
        return f,o,a,cm,assert_list,assume_list,assert_key



def simplification_expr(e):

    args=expr_args(e)

    op=expr_op(e)

    list_expr=[]

    list_expr.append(op)

    if len(args)==0:

        return e

    else:

        for arg in args:

            arg = simplification_axioms(arg)

            arg = simplification_expr(arg)

            list_expr.append(arg)
   
    if list_expr[0]=='ite':

       list_expr = simplification_axioms(list_expr)
            
    return list_expr


 

def getAssertAssume(f,o,a,cm):
    new_o={}
    new_a=[]
    new_f={}
    assert_list = []
    assume_list = []
    assert_key = []

    for x in f:
        if x.find('_assertion')<0 and x.find('_assumption')<0:
            new_f[x]=f[x]


    for x in o:
        if x.find('_assertion')>0  and o[x][-1][0].find('_assertion')<0:
            assert_list.append(o[x])
        elif x.find('_assumption')>0 and o[x][-1][0].find('_assumption')<0:
            assume_list.append(o[x])
        else:
            new_o[x]=o[x]

    
    for x in a:

        if x[0]=='i1':

           if x[3][0].find('_assertion')>0:

              assert_list.append(x)

           elif x[3][0].find('_assumption')>0:

              assert_list.append(x)

           else:

              new_a.append(x) 

        elif x[0]=='i0':

           if x[-2][0].find('_assertion')<0 and x[-2][0].find('_assumption')<0:

              new_a.append(x)

        else:

           new_a.append(x) 


    return new_f, new_o, new_a, assert_list, assume_list, assert_key








def simplification_axioms(e):
    
    flag = None
    
    Cond =None

    Case1 = None

    Case2 = None

    if e[0]=='ite':

        arg_list=expr_args(e)

        if arg_list[0][0]=='ite':

           Cond = simplification_axioms(arg_list[0])

        else:
           
           if arg_list[0][0]=='=':

              leftSide = expr2string1(arg_list[0][1])

              rightSide = expr2string1(arg_list[0][2])

              result=simplify(leftSide+'-'+rightSide)


              if is_number(result):

                 if int(result)==0:

                    flag = True

                 else:

                    flag = False

              else:

                 Cond = arg_list[0]


           else:

              Cond = arg_list[0]


        if arg_list[1][0]=='ite':

           Case1 = simplification_axioms(arg_list[1])

        else:

           Case1 = arg_list[1]

        if arg_list[2][0]=='ite':

           Case2 = simplification_axioms(arg_list[2])

        else:

           Case2 = arg_list[2]


        if flag==True:

           return Case1

        elif flag==False:

           return Case2

        else:

           return ['ite']+[Cond]+[Case1]+[Case2]

    else:

       return e












def simply_output_axioms_fn(f,o,a):

    for x in o:

        o[x][-1] = simplification_axioms(o[x][-1])

    #for x in a:

    #    x[-1] = simplification_axioms(x[-1])






    
       
    




def checkCondition(e):
    if e[0]=='=':
       arg1=e[1]
       arg2=e[2]
       if arg1==arg2:
          return True
       else:
          return None
    elif e[0]=='!=':
       arg1=e[1]
       arg2=e[2]
       if arg1==arg2:
          return False
       else:
          return None
    return None


	


def simplifyAxioms(e):
    if e[0]=='ite':
        arg_list=expr_args(e)
        if checkCondition(arg_list[0]) == True:
           return e,arg_list[1]
        elif checkCondition(arg_list[0]) == False:
           return e,arg_list[2]
        else:
           return None, None
    return None, None






def output_axioms_fn(f,o,a):
    #print('Output in prefix notation:')
    #print('1. Frame axioms:')
    #eqset2string(f)
    #print('\n2. Output equations:')
    #eqset2string(o)
    #print('\n3. Other axioms:')
    #for x in a: 
    #    print wff2string(x)
    print('\nOutput in normal notation:')
    print('1. Frame axioms:')
    eqset2string1(f)
    print('\n2. Output equations:')
    eqset2string1(o)
    print('\n3. Other axioms:')
    for x in a: 
        print(wff2string1(x))




def output_axioms_fn_print(f,o,a):
    Output_val=''
    Output_val+='\nOutput in normal notation:\n'
    Output_val+='\n1. Frame axioms:\n'
    Output_val+=eqset2string1Print(f)+"\n"
    Output_val+='\n2. Output equations:\n'
    Output_val+=eqset2string1Print(o)+"\n"
    Output_val+='\n3. Other axioms:\n'
    for x in a: 
        Output_val+=wff2string1(x)+"\n"
    return Output_val






def organizeOutput(f,o,a,vfacts):
    array_list=[]
    new_f={}
    duplicate_map={}
    new_f={}
    new_o={}
    new_a=[]
    for vfact in vfacts.keys():
        info_list=vfacts[vfact]
        if type(info_list) is dict:
            for info in info_list:
                element_list=info_list[info]
                if type(element_list) is list and len(element_list)>0:
                    if element_list[1]=='array' and '_PROVE' not in info and '_ASSUME' not in info and len(element_list)==2:
                        array_list.append(info)
        else:
            if info_list[1]=='array' and '_PROVE' not in vfact and '_ASSUME' not in vfact and len(element_list)==2:
                array_list.append(vfact)
    

    for e in f:
        if isArrayFunction(e)==True:
            if len(array_list)>0:
                new_f[e]=f[e]
        else:
            new_f[e]=f[e]
    for e in o:
        if isArrayFunction(e)==True:
            if len(array_list)>0:
                new_o[e]=o[e]
        else:
            new_o[e]=o[e]
    for e in a:
        if e[0]=='i1':
            if isArrayFunction(e[3][0])==True:
                if len(array_list)>0:
                    new_a.append(e)
            else:
                new_a.append(e)
        elif e[0]=='i0':
            if isArrayFunction(e[2][0])==True:
                if len(array_list)>0:
                    new_a.append(e)
            else:
                new_a.append(e)
        else:
            new_a.append(e)
    
    return new_f,new_o,new_a



def update__VERIFIER_nondet_stmt(e,var_map):
    args=expr_args(e)
    if '__VERIFIER_nondet' in e[0] and len(args)==0:
        if e[0] in var_map.keys():
            VC=var_map[e[0]]
            VC=VC+1
            key=e[0]
            var_map[key]=VC
            e[0] = e[0]+str(VC)
            return e
        else:
            key=e[0]
            var_map[key]=2
            e[0] = e[0]+str(2)
            return e
    else:
        return e[:1]+list(update__VERIFIER_nondet_stmt(x,var_map) for x in expr_args(e))


"""
Recurrences Solving Module
#Add by Pritom Rajkhowa
#June 8

Test cases

Test Case 1

#e1=['i1', 2, '_n1', ['a3', ['+', ['_n1'], ['1']]], ['+', ['a3', ['_n1']], ['1']]]
#e2=['i0', 0, ['a3', ['0']], ['0']]

Test Case 2

#e1=['i1', 2, '_n1', ['a3', ['+', ['_n1'], ['1']]], ['*', ['a3', ['_n1']], ['+', ['_n1'], ['1']]]]
#e2=['i0', 0, ['a3', ['0']], ['1']]

Test Case 3

#e1=['i1', 2, '_n1', ['t3', ['+', ['_n1'], ['1']]], ['+', ['t3', ['_n1']], ['2']]]
#e2=['i0', 0, ['a3', ['0']], ['1']]

Test Case 4

#e1=['i1', 2, '_n1', ['a3', ['+', ['_n1'], ['1']]], ['*', ['a3', ['_n1']], ['2']]]
#e2=['i0', 0, ['a3', ['0']], ['1']]

"""
def solve_rec(e1,e2):
        global fun_call_map
        lefthandstmt=None
        righthandstmt=None
        righthandstmt_d=None
        lefthandstmt_base=None
        righthandstmt_base=None
        righthandstmt_base_d=None
        variable=None
        closed_form_soln=None
        if e1[0]=='i1':
                lefthandstmt=expr2string1(e1[3])
                righthandstmt=expr2string1(e1[4])
                lefthandstmt=lefthandstmt.strip()
                righthandstmt=righthandstmt.strip()
                variable=e1[2]
                if lefthandstmt.find('_PROVE')>0:
                       return None
                elif lefthandstmt.find('_ASSUME')>0:
                       return None
                if 'ite' not in righthandstmt and '>' not in righthandstmt and '<' not in righthandstmt and '==' not in righthandstmt and '!=' not in righthandstmt and '|' not in righthandstmt and '&' not in righthandstmt: 

                        lefthandstmt=simplify(lefthandstmt)
                        righthandstmt=simplify(righthandstmt)
                        variable=simplify(variable)
                else:
                        if '|' not in righthandstmt and '&' not in righthandstmt and '<<' not in righthandstmt and '>>' not in righthandstmt:
                           righthandstmt=expr2stringSimplify(e1[4])
                        righthandstmt=righthandstmt.strip()
                        if 'ite' not in righthandstmt and '>' not in righthandstmt and '<' not in righthandstmt and '==' not in righthandstmt and '<' not in righthandstmt and '==' not in righthandstmt and '!=' not in righthandstmt and '|' not in righthandstmt and '&' not in righthandstmt: 

                                lefthandstmt=simplify(lefthandstmt)
                                righthandstmt=simplify(righthandstmt)
                                variable=simplify(variable)
                        else:
                                lefthandstmt=None
                                righthandstmt=None
                                variable=None
        if e2[0]=='i0':
                lefthandstmt_base=expr2string1(e2[2])
                righthandstmt_base=expr2string1(e2[3])
                variable_list=[]
                expr2varlist(e2[3],variable_list)
                lefthandstmt_base=lefthandstmt_base.strip()
                righthandstmt_base=righthandstmt_base.strip()
                if 'ite' in righthandstmt_base or '|' in righthandstmt_base or '&' in righthandstmt_base or '<<' in righthandstmt_base or '>>' in righthandstmt_base: 
                     return None
                lefthandstmt_base=simplify(lefthandstmt_base)
                righthandstmt_base=simplify(righthandstmt_base)

        if variable is not None and lefthandstmt is not None and righthandstmt is not None and lefthandstmt_base is not None and righthandstmt_base is not None:
                righthandstmt_d=righthandstmt
                righthandstmt_base_d=righthandstmt_base
                term1=lefthandstmt.subs(simplify(str(variable)+"+1"),0)
                term2=lefthandstmt.subs(simplify(str(variable)+"+1"),simplify(variable))
                if term1==lefthandstmt_base and  str(term2) in str(righthandstmt):
                        righthandstmt=simplify(righthandstmt).subs({simplify(term2):simplify('T(n)'),simplify(variable):simplify('n')})
                        result=None
			    #Try to solve recurrences
                try:
				
                                result = getSympyCache(righthandstmt,righthandstmt_base)
                                #result = None
                                
                                if result is None:
                                    #result=recurreSolver_wolframalpha(righthandstmt,righthandstmt_base,variable_list)
                                    result=recurreSolver_sympy(righthandstmt,righthandstmt_base)
                                    #result = None
				#if result is None:
					#result=recurreSolver_sympy(righthandstmt,righthandstmt_base)
					#result=recurreSolver_wolframalpha(righthandstmt,righthandstmt_base,variable_list)
                except ValueError:
                    result=None
                if result is not None:
                    result=substituteValue(simplify_sympy(result),simplify('n'),simplify(variable))
                    if "**" in str(result):
                       result=translatepowerToFun(str(result))
                    expression=str(str(term2)+"="+str(result))
                    fun_call_map={}
                    parser = c_parser.CParser()
                    ast = parser.parse("void test(){"+expression+";}")
                    statement_temp=ast.ext[0].body.block_items[0]                               
                    closed_form_soln = construct_expressionC(e1[1],e1[2],expr_replace_power(eval(expressionCreator_C(statement_temp.lvalue))),expr_replace_power(eval(expressionCreator_C(statement_temp.rvalue))))
                    #tree = p.parse_expression(expression)
                    #closed_form_soln=construct_expression(tree,e1[1],e1[2])
        #return None
        return closed_form_soln



# expr_replace(e,e1,e2): replace all subterm e1 in e by e2


def expr_replace_power(e): #e,e1,e2: expr
    args=expr_args(e)
    op=expr_op(e)
    if len(args)>0:
        if op=='power' or 'power_' in op :
            return eval("['**']")+list(expr_replace_power(x) for x in expr_args(e))
        else:
            return e[:1]+list(expr_replace_power(x) for x in expr_args(e))
    else:
        return e




#get variable
def expr2varlist(e,variable_list):
    args=expr_args(e)    
    op=expr_op(e)
    if len(args)==0:
    	if '_n' not in op and is_number(op)==False:
    		variable_list.append(op)
    else:
        if op=='and' or op=='or':
            if len(args)==1:
               expr2varlist(args[0],variable_list)
            else:
                for x in args:
                    expr2varlist(x,variable_list)
        elif op=='not' and len(args)==1:
            expr2varlist(args[0],variable_list)
        elif op=='implies' and len(args)==2:
        	expr2varlist(args[0],variable_list)
        	expr2varlist(args[1],variable_list)
        elif op in _infix_op and len(args)==2:
        	expr2varlist(args[0],variable_list)
        	expr2varlist(args[1],variable_list)
        else:
            for x in args:
                expr2varlist(x,variable_list)


def getSympyCache(expression,base_expression):
        #print '~~~~~~~~~~~~~~'
        #print expression
        #print base_expression
        #print '~~~~~~~~~~~~~~'
	#cache_map={'(n + 1)**3 + T(n)':['0','(n**2*(n + 1)**2)/2'],'(i + n + 1)**3 + T(n)':['N_1','N_1 + (n*(n + (1 + 2*i) )*(- (2 - 2*i)  + n*(n + (1 + 2*i) )))/4']}
	cache_map={'(n + 1)**3 + T(n)':['0','(n**2*(n + 1)**2)/4'],'T(n) - 1':['N_1','N_1 - n'],'4000 + T(n)':['0','4000*n'],'2000 + T(n)':['0','2000*n']}
	for element in cache_map.keys():
		if simplify(element)==simplify(expression):
                        try:
                                        
                            return simplify(cache_map[element][1]).subs(simplify(cache_map[element][0]),simplify(base_expression))
                            
                        except ValueError:
                            return None
			
	return None


"""
 
#Solving Recurrences using sympy
 
"""
def recurreSolver_sympy(righthandstmt,righthandstmt_base):
    expression="T(n+1)-("+str(righthandstmt)+")"
    #print expression
    f=simplify(expression)
	#Register n as Symbol
    n=Symbol('n')
	#Register T as Function
    T=Function('T')
    result=None
	#Converting String to Sympy Expression
    terminationList={sympify("T(0)"):righthandstmt_base}
	#Try to solve recurrences
    try:
                result=rsolve(f, T(n), terminationList)
                flag=False
                flag=isConstInResult( str(result) )
                if flag==False and result is not None and 'RisingFactorial' not in str(result) and 'binomial' not in str(result) and 'gamma' not in str(result) and 'rgamma' not in str(result) and 'gammaprod' not in str(result) and 'loggamma' not in str(result) and 'beta' not in str(result) and 'superfac' not in str(result) and 'barnesg' not in str(result):
                        result=simplify(result)
                else:
                        result=None
                        #writeLogFile( "j2llogs.logs" , "\nFailed to find close form solution\n" )
    except ValueError:
        result=None
		#writeLogFile( "j2llogs.logs" , "\nFailed to find close form solution\n" )

    return result





#Parsing Method Starts

# define some basic operand expressions
number = Regex(r'\d+(\.\d*)?([Ee][+-]?\d+)?')
ident = Word(alphas+'_', alphanums+'_')
#fn_call = ident + '(' + Optional(delimited_list(expr)) + ')'

# forward declare our overall expression, since a slice could 
# contain an arithmetic expression
expr = Forward()
#slice_ref = '[' + expr + ']'

slice_ref = '[' + expr + ZeroOrMore("," + expr) + ']'

# define our arithmetic operand
operand = number | Combine(ident + Optional(slice_ref))
#operand = number | fn_call | Combine(ident + Optional(slice_ref))
inequalities = oneOf("< > >= <= = == !=")

# parse actions to convert parsed items
def convert_to_pow(tokens):
    tmp = tokens[0][:]
    ret = tmp.pop(-1)
    tmp.pop(-1)
    while tmp:
        base = tmp.pop(-1)
        # hack to handle '**' precedence ahead of '-'
        if base.startswith('-'):
            ret = '-power(%s,%s)' % (base[1:], ret)
        else:
            ret = 'power(%s,%s)' % (base, ret)
        if tmp:
            tmp.pop(-1)
    return ret

def unary_as_is(tokens):
    return '(%s)' % ''.join(tokens[0])

def as_is(tokens):
    return '%s' % ''.join(tokens[0])


# simplest infixNotation - may need to add a few more operators, but start with this for now
arith_expr = infixNotation( operand,
    [
    ('-', 1, opAssoc.RIGHT, as_is),
    ('**', 2, opAssoc.LEFT, convert_to_pow),
    ('-', 1, opAssoc.RIGHT, unary_as_is),
    ((inequalities,inequalities), 3, opAssoc.LEFT, as_is),
    (inequalities, 2, opAssoc.LEFT, as_is),
    (oneOf("* /"), 2, opAssoc.LEFT, as_is),
    (oneOf("+ -"), 2, opAssoc.LEFT, as_is),
    (oneOf('and or'), 2, opAssoc.LEFT, as_is),
    ])
#('-', 1, opAssoc.RIGHT, as_is),
# now assign into forward-declared expr
expr <<= arith_expr.setParseAction(lambda t: '(%s)' % ''.join(t))

"""
#expression="2**3"
#expression="2**-3"
#expression="2**3**x5"
#expression="2**-3**x6[-1]"
#expression="2**-3**x5+1"
#expression="(a+1)**2"
#expression="((a+b)*c)**2"
#expression="B**2"
#expression="-B**2"
#expression"(-B)**2"
#expression="B**-2"
#expression="B**(-2)"
#expression="((Z**(_N1+1)-1)/(Z-1))*(Z-1))"
#expression="((_N1+1)**2)<=X"
#expression="_n2*_n3*_N1(_n2, _n3)**2/2"
#translatepowerToFun(expression)
#expression="_n2*_n3*_N1(_n2, X(_n3))**2/2"

#expression="(((2.00000000000000)+_n2*_n3*_N1(_n2, X(_n3))**2/2))"

"""

def translatepowerToFun(expression):
    if "**" in expression:
        try:
            backup_expression=expression
            if ("<" in  expression or ">" in  expression) and '/' not in expression :
                expression=simplify(expression)
            expression=transferToFunctionSyntax(str(expression))
            xform = expr.transformString(expression)[1:-1]
            #xform = expr.transformString(expression)
            xform=xform.replace('[','(')
            expression=xform.replace(']',')')
        except Exception as e:
            expression=backup_expression
   	#print expression
    return expression






"""
Example 1:
>>> expression="x(n)+(y(n)+1)*n"
>>> transferToMathematicaSyntax(expression)
'x[n]+(y[n]+1)*n'

Example 2:

>>> expression="x(n(a,b),a,b)+2^(y(_N1(a,b),a,b)+1)"
>>> transferToMathematicaSyntax(expression)
'x[n[a,b],a,b]+2^(y[_N1[a,b],a,b]+1)'

Example 3:

>>> expression="x(n)+(y(n)/(_N1(n)))"
>>> transferToMathematicaSyntax(expression)
'x[n]+(y[n]/(_N1(n)))'

"""

#Changing function of the formate f(n) to f[n]. It assist the pasring 

def transferToFunctionSyntax(expression):
	if "(" in expression and ")" in expression:
		p = regex.compile(r'\b[a-zA-Z_]\w*(\((?>[^()]|(?1))*\))')
		result=(p.sub(lambda m: m.group().replace("(", "[").replace(")", "]"), expression))
	else:
		result=expression
	return result


#Parsing Method Ends

def isConstInResult( variable ):
	status=False
	find=regex.compile(r'C\d')
	group = find.search(variable)
	if group is not None:
		status=True
	return status


def simplify_sympy(expression):
        #if '/' in str(expression) and '>' not in str(expression) and '<' not in str(expression) and '=' not in str(expression):  
        if '<<' in str(expression) or '>>' in str(expression) or 'ite' in str(expression) or 'and' in str(expression) or '&' in  str(expression) or '|' in str(expression) or '^' in str(expression):
            return expression 
        try:
            sympify(expression)
        except Exception as e:
            return expression
        
        if sympify(expression)==True or sympify(expression)==False:
                return expression        
        if '/' in str(expression):
        	expression,flag=expressionChecking(expression)
        	if flag==True:
        		expression_mod=expression 
        	else:
        		expression_mod=powsimp(expression)
        else:
            if 'array' not in str(expression):
                expression_mod=powsimp(expression)
            else:
                expression_mod=expression 
    
        if '/' not in str(expression_mod) and 'E' not in str(expression_mod) and 'e' not in str(expression_mod):
                expression=expression_mod
        if '/' in str(expression):
                no,deno=fraction(together(expression))
                no=sympify(no).expand(basic=True)
                deno=sympify(deno).expand(basic=True)
                if deno==1:
                        expression,flag=expressionChecking(expression)
                        if flag==True:
                                return expression
				#return pow_to_mul(powsimp(expression))
                        else:
                                return pow_to_mul(powsimp(expression))
                                #return pow_to_mul(powsimp(no))
                else:
                        return Mul(pow_to_mul(powsimp(no)), Pow(pow_to_mul(powsimp(deno)), -1), evaluate=False)
	
        else:
                #return str(sympify(expression).expand(basic=True))
                if type(expression) is str:
                    return expression
                else:
                    expressiontemp=sympify(expression).expand(basic=True)
                    if '/' in str(expressiontemp):
                            return pow_to_mul(powsimp(sympify(expression)))
                    else:
                            return pow_to_mul(powsimp(sympify(expression).expand(basic=True)))
	

def substituteValue(expression,key,value):
	if '/' in str(expression):
		#no,deno=fraction(together(expression))
		no,deno=fraction(expression)
		no=sympify(no).expand(basic=True)
		no=no.subs(simplify(key),simplify(value))
		deno=deno.subs(simplify(key),simplify(value))
		if deno==1:
			return powsimp(no)
		else:
                 	return Mul(powsimp(no), Pow(powsimp(deno), -1), evaluate=False)
	
	else:
		return simplify(expression).subs(simplify(key),simplify(value))



"""
Expanding algebraic powers
"""

def pow_to_mul(expression):
    """
    Convert integer powers in an expression to Muls, like a**2 => a*a(Only for Squre).
    """
    #expression=simplify(expression).expand(basic=True)
    #expression=simplify(expression)
    pows=list(expression.atoms(Pow))
    if any(not e.is_Integer for b, e in (i.as_base_exp() for i in pows)):
    	#A power contains a non-integer exponent
    	return expression
    repl=None
    for b,e in (i.as_base_exp() for i in pows):
    	if e==2:
    		repl = zip(pows,((Mul(*[b]*e,evaluate=False)) for b,e in (i.as_base_exp() for i in pows)))
    if repl is not None:
    	return expression.subs(repl)
    else:
    	return expression

def translatepowerToFunCheck(expression):
    if "**" in expression:
    	expression=transferToFunctionSyntax(str(expression))
    	xform = expr.transformString(expression)[1:-1]
    	xform=xform.replace('[','(')
    	expression=xform.replace(']',')')
   	#print expression
    return expression

#expression="(A+B+((Z**(K)-1)/(Z-1))*(Z-1))"
expression="((Z**(K)-1)/(Z-1))*(Z-1)"
expression="(Z/2)*6<=Z"
expression="r6(_n2)>=(((2**-(_n2))*((2**_N1)*B))/2)"
#expressionChecking(expression)
def expressionChecking(expression):
    if '(((((((' not in str(expression):
        if "**" in str(expression):
           expression=translatepowerToFunCheck(str(expression))
        #p = getParser()
        parser = c_parser.CParser()
        #tree = p.parse_expression(expression)
        ast = parser.parse("void test(){"+str(expression)+";}")
        statement_temp=ast.ext[0].body.block_items[0]
        #expr_wff=eval(expressionCreator(tree)) 
        expr_wff = eval(expressionCreator_C(statement_temp))
        flag=False
        return expr2simplified(expr_wff,flag)
    else:
        return str(expression),False

def construct_expressionC(postion,variable,e1,e2):
    expression=[]
    expression.append('i2')
    expression.append(postion)
    expression.append(variable)
    expression.append(e1)
    expression.append(e2)
    return expression

def construct_expression(tree,postion,variable):
	expression=""
	if type(tree) is m.Assignment:
		expression="['i2',"+str(postion)+",'"+variable+"',"+expressionCreator(tree.lhs)+","+expressionCreator(tree.rhs)+"]"
	return eval(expression)



def construct_expression_normalC(e):
    if e is not None:
       expression=[]
       expression.append('s0')
       expression.append(e)
       return expression
    else:
       return None


	
def construct_expression_normal(tree):
	if tree is not None:
		expression=""
		if type(tree) is m.Relational:
			expression="['s0',"+expressionCreator(tree)+"]"
		return eval(expression)
	else:
		return None


"""

Program Expression to a Array of Statement Compatible to Translator Program 

"""

fun_call_map={}
current_fun_call=None
defineMap={}


def expressionCreator_C(statement):
    expression=""
    global defineMap
    global defineDetaillist
    global fun_call_map
    global current_fun_call
    if type(statement) is c_ast.ID:
       if statement.name in defineMap.keys():
    	   value = defineMap[statement.name]
    	   return str(eval("expres('"+value+"')"))
       else:
          return str(eval("expres('"+statement.name+"')"))
    elif type(statement) is c_ast.Constant:
        if statement.type=='char':
                if str(statement.value)==str("'\\0'"):
                    return str(eval("expres('0')"))
                else:
                    return "['char',expres("+statement.value+")]"
        elif statement.type=='float':
                if statement.value[-1]=='f':
                   #return "expres('"+str(round(float(statement.value[:-1]), 7))+"')"
                    return str(eval("expres('"+str(statement.value[:-1])+"')"))
                #return "expres('"+str(float(statement.value))+"')"
                return str(eval("expres('"+str(statement.value)+"')"))
        elif statement.type=='double':
                #return "expres('"+str(float(statement.value))+"')"
                return str(eval("expres('"+str(statement.value)+"')"))
        else:
                if is_hex(statement.value) is not None:
                    return str(eval("expres('"+is_hex(statement.value)+"')"))
                else:
                    return str(eval("expres('"+statement.value+"')"))
    elif type(statement) is c_ast.FuncCall:
        parameter=''
        parameter_list=[]
        defineDetaillist=[]
        defineDetailtemp=[]
        parameter_list.append('int')
        if statement.args is not None:
            for param in statement.args.exprs:
                if type(param) is c_ast.ID:
                    parameter_list.append('int')
                    if param.name in defineMap.keys():
                        param.name = defineMap[param.name]
                    if parameter=='':
                        parameter = str(eval("expres('"+param.name+"')"))
                    else:
                        parameter += ","+str(eval("expres('"+param.name+"')"))
                elif type(param) is c_ast.Constant:
                    parameter_list.append('int')
                    if parameter=='':
                       if is_hex(param.value) is not None:
                          parameter = str(eval("expres('"+is_hex(param.value)+"')"))
                       else:
                          parameter = str(eval("expres('"+param.value+"')"))
                    else:
                       if is_hex(param.value) is not None:
                          parameter += ","+str(eval("expres('"+is_hex(param.value)+"')"))
                       else:
                          parameter += ","+str(eval("expres('"+param.value+"')"))

                elif type(param) is c_ast.UnaryOp:
                     if parameter=='':
                                    
                        parameter = str(eval("expres('"+param.op+"',["+expressionCreator_C(param.expr)+"])"))
                     else:
                        parameter +=','+str(eval("expres('"+param.op+"',["+expressionCreator_C(param.expr)+"])"))
		        
                elif type(param) is c_ast.BinaryOp:
                    if parameter=='':
                        parameter =expressionCreator_C(param)
                    else:
                        parameter +=','+expressionCreator_C(param)
                elif type(param) is c_ast.FuncCall:
            
                    if parameter=='':
                       #param.show()
                       parameter =expressionCreator_C(param)
                    else:
                       #param.show()
                       parameter +=','+expressionCreator_C(param)
                else:
                     if type(param) is c_ast.ArrayRef:
                        parameter_list.append('int')
                        degree=0
                        stmt,degree=createArrayList_C(param,degree)
                        if parameter=='':
                           parameter = str(eval("expres('d"+str(degree)+'array'+"',["+stmt+"])"))
                        else:
                           parameter += ","+str(eval("expres('d"+str(degree)+'array'+"',["+stmt+"])"))
				
			    #print '@@@@@@@@@@@RamRam'
				#print param.show()
				#print '@@@@@@@@@@@'
		
            if 'uniform' in statement.name.name:
                parameter="['"+statement.name.name+"'],"+parameter
                return "['RV',"+parameter+"]"
            elif 'gauss' in statement.name.name:
                parameter="['"+statement.name.name+"'],"+parameter
                return "['RV',"+parameter+"]"
            else:
                defineDetailtemp.append(statement.name.name)
                defineDetailtemp.append(len(parameter_list)-1)
                defineDetailtemp.append(parameter_list)
                defineDetaillist.append(defineDetailtemp)                
                #if statement.name.name in fun_call_map.keys() and statement.name.name != current_fun_call and '__VERIFIER_nondet_' not in statement.name.name:
                #    fc_count=fun_call_map[statement.name.name]
                #    fc_count+=1
                #    fun_call_map[statement.name.name]=fc_count
                #    return "['"+statement.name.name+"_"+str(fc_count)+"',"+parameter+"]"
                #else:
                #    fun_call_map[statement.name.name]=0
                return "['"+statement.name.name+"',"+parameter+"]"
        else:
                if '__VERIFIER_nondet_' not in statement.name.name:
                    defineDetailtemp.append(statement.name.name)
                    defineDetailtemp.append(len(parameter_list)-1)
                    defineDetailtemp.append(parameter_list)
                    defineDetaillist.append(defineDetailtemp)
		#if statement.name.name in fun_call_map.keys() and statement.name.name != current_fun_call and '__VERIFIER_nondet_' not in statement.name.name:
                #    fc_count=fun_call_map[statement.name.name]
                #    fc_count+=1
                #    fun_call_map[statement.name.name]=fc_count
                #    return str(eval("expres('"+statement.name.name+"_"+str(fc_count)+"'"+")"))
                #else:
                #    fun_call_map[statement.name.name]=0  
                return str(eval("expres('"+statement.name.name+"'"+")"))
                    
    elif type(statement) is c_ast.ArrayRef:
        degree=0
       	stmt,degree=createArrayList_C(statement,degree)
        return str(eval("expres('d"+str(degree)+'array'+"',["+stmt+"])"))
    else:
        if type(statement) is c_ast.Cast:
            if statement.to_type.type.type.names[0]=='float':
                return "['"+"_ToReal"+"',"+expressionCreator_C(statement.expr)+"]"
            elif statement.to_type.type.type.names[0]=='double':
                return "['"+"_ToReal"+"',"+expressionCreator_C(statement.expr)+"]"
            elif statement.to_type.type.type.names[0]=='int':
                return "['"+"_ToInt"+"',"+expressionCreator_C(statement.expr)+"]"
        else:
            
            if statement.op in ['+','-','*','/','%']:
                expression="expres('"
                expression+=statement.op
                if type(statement) is c_ast.BinaryOp:
                    expression+="',["+expressionCreator_C(statement.left)
                    expression+=','+expressionCreator_C(statement.right)
                else:
                    expression+="',["+expressionCreator_C(statement.expr)
                expression+='])'
                expression=str(eval(expression))
                return expression
            else:
                #if statement.op == '!=':
                #    statement=c_ast.UnaryOp(op='!', expr=c_ast.BinaryOp(op='==',left=statement.left, right=statement.right))

                expression="['"
                if statement.op == '&&':
                    expression+='and'
                elif statement.op == '||':
                    expression+='or'
                elif statement.op == '!':
                    expression+='not'
                else:
                    expression+=statement.op
                if type(statement) is c_ast.BinaryOp:
                    expression+="',"+expressionCreator_C(statement.left)

                    expression+=','+expressionCreator_C(statement.right)
                    expression+=']'
                else:
                    expression="expres('"
                    if statement.op == '!':
                            expression+='not'
                    else:
                            expression+=statement.op
                    statement.show()
                    print('=================')
                    expression+="',["+expressionCreator_C(statement.expr)+"]"
                    expression+=')'
                    expression=str(eval(expression))
                return expression




"""

Construct Array List

"""
def createArrayList_C(statement,degree):
	if type(statement) is c_ast.ArrayRef:
		degree=degree+1
		stmt=''
		if type(statement.name) is c_ast.ArrayRef:
                   stmt,degree=createArrayList_C(statement.name,degree)
                   if type(statement.subscript) is c_ast.ID:
                      stmt+=",expres('"+statement.subscript.name+"')"
                   elif type(statement.subscript) is c_ast.BinaryOp:
                      stmt+=","+expressionCreator_C(statement.subscript)
                   else:
                      stmt+=",expres('"+statement.subscript.value+"')"
                   return stmt,degree
		else:
			if type(statement.name) is c_ast.ID:
				if type(statement.subscript) is c_ast.ID:
					stmt+="expres('"+statement.name.name+"')"+",expres('"+statement.subscript.name+"')"
					return stmt,degree
				elif type(statement.subscript) is c_ast.BinaryOp:
					stmt+="expres('"+statement.name.name+"')"+","+expressionCreator_C(statement.subscript)
					return stmt,degree
				else:
                                        if type(statement.subscript) is c_ast.ArrayRef:
                                            temp_degree=0
                                            temp_stmt,temp_degree=createArrayList_C(statement.subscript,temp_degree)
                                            stmt+="expres('"+statement.name.name+"')"+","+"expres('d"+str(temp_degree)+'array'+"',["+temp_stmt+"])"
                                            return stmt,degree 
                                        else:
                                            stmt+="expres('"+statement.name.name+"')"+",expres('"+statement.subscript.value+"')"
                                            return stmt,degree
			else:
				if type(statement.name) is c_ast.FuncCall:
					if type(statement.subscript) is c_ast.FuncCall:
						stmt+=expressionCreator_C(statement.name)+","+expressionCreator_C(statement.subscript)
					elif type(statement.subscript) is c_ast.BinaryOp:
						stmt+=expressionCreator_C(statement.name)+","+expressionCreator_C(statement.subscript)
					else:
						stmt+=expressionCreator_C(statement.name)+",expres('"+statement.subscript.value+"')"
				else:
					stmt+="expres('"+statement.name.value+"')"+",expres('"+statement.subscript.value+"')"
				return stmt,degree
	else:
		return "expres('"+statement.name+"')",degree






"""
Recurrence Solver After Translation
"""
def rec_solver(f,o,a):
    global fun_call_map
    constant_fun_map={}
    equation_map={}
    base_map={}
    for axiom in a:
        if axiom[0]=='i1':
             lefthandstmt=expr2string1(axiom[3])
             lefthandstmt=lefthandstmt.strip()
             equation_map[str(simplify(lefthandstmt))]=axiom
        if axiom[0]=='i0':
             lefthandstmt=expr2string1(axiom[2])
             lefthandstmt=lefthandstmt.strip()
             base_map[str(simplify(lefthandstmt))]=axiom
        if axiom[0]=='s1':
             equ=expr2string1(axiom[1])
             if '->' in equ:
                 axiomes=equ.split('->')
                 axiomes[0]=simplify(str(axiomes[0]))
                 if '<'  in str(axiomes[0]):
                    variables=str(axiomes[0]).split('<')
                 elif '>'  in str(axiomes[0]):
                    variables=str(axiomes[0]).split('>')
                 variables[0]=variables[0].strip()
                 variables[1]=variables[1].strip()
                 constant_fun_map[variables[0]]=variables[1]
    while True:
        solution_map={} 
        for equation in equation_map:
            e1=equation_map[equation]
            equation_base=str(simplify(equation).subs(simplify(str(e1[2])+"+1"),0))
            if equation_base in base_map.keys():
                e2=base_map[equation_base]
                result=solve_rec(e1,e2)
                #result = None
                if result is not None:
                    a.remove(base_map[equation_base])
                    del base_map[equation_base]
                    solution_map[equation]=result
    
        for equation in solution_map:
            a.remove(equation_map[equation])
            del equation_map[equation]
            e=solution_map[equation]
            e1=copy.deepcopy(e)
            variable=e[2]
            a=solnsubstitution(a,e[3],e[4])
            constant=constant_fun_map[variable]
            #p = getParser()
            #tree = p.parse_expression(constant)
            #constant=eval(expressionCreator(tree))
            fun_call_map={}
            parser = c_parser.CParser()
            ast = parser.parse("void test(){"+str(constant)+";}")
            statement_temp=ast.ext[0].body.block_items[0]
            constant=eval(expressionCreator_C(statement_temp))
            variable_list=eval("expres('"+variable+"')")
            e1[3]=expr_replace(e1[3],variable_list,constant)
            e1[4]=expr_replace(e1[4],variable_list,constant)
            a=solnsubstitution(a,e1[3],e1[4])
            for x in o:
                stmt=o[x]
                stmt[2]=expr_replace(stmt[2],e1[3],e1[4])
        if len(equation_map)==0 or len(solution_map)==0:
           break
    return f,o,a,constant_fun_map

""" 
#Function to replace variable by constant
#Test Case
#e=['a', ['<', ['x2', ['_n1']], ['y2', ['_n1']]]]
#variable='_n1'
#constant='_N1'
#expr_replace_const(e,variable,constant)
"""

def expr_replace_const(e,variable,constant):
	if e[:1]==expres(variable):
		e[:1]=expres(constant)
	return e[:1]+list(expr_replace_const(x,variable,constant) for x in expr_args(e))


def get_All_Var(e,var_map):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
    	if is_number(op)==False and is_hex(op)==None and op not in _base:
        	var_map.append(op)
    else:
        if op=='and' or op=='or':
            if len(args)==1:
                get_All_Var(args[0],var_map)
            else:
            	for x in args:
            		get_All_Var(x,var_map)
        elif op=='not' and len(args)==1:
            get_All_Var(args[0],var_map)
        elif op=='implies' and len(args)==2:
            get_All_Var(args[0],var_map)
            get_All_Var(args[1],var_map)
        elif op in _infix_op and len(args)==2:
            get_All_Var(args[0],var_map)
            get_All_Var(args[1],var_map)
        else:
        	if is_number(op)==False and is_hex(op)==None and op not in _base:
        		var_map.append(op)
        	for x in args:
        		get_All_Var(x,var_map)



#substituting close form solution in rest of the axiomes
def solnsubstitution(axioms,key,substituter):
    update_axioms=[]
    for axiom in axioms:
        if axiom[0]!='i0' and axiom[0]!='i1':
           update_axioms.append(expr_replace(axiom,key,substituter))
        else:
           if axiom[0]=='i1':
              axiom[4]=expr_replace(axiom[4],key,substituter)
              update_axioms.append(axiom)
           elif axiom[0]=='i0':
              axiom[3]=expr_replace(axiom[3],key,substituter)
              update_axioms.append(axiom)
           else:
              update_axioms.append(axiom)
    return update_axioms



    
def solnsubstitution_Array(axioms,key,substituter):
    update_axioms=[]
    for axiom in axioms:
        if axiom[0]!='i0' and axiom[0]!='i1':
            update_axioms.append(expr_array_replace(axiom,key,substituter))
        else:
            if axiom[0]=='i1':
               axiom[4]=expr_array_replace(axiom[4],key,substituter)
               update_axioms.append(axiom)
            elif axiom[0]=='i0':
               axiom[3]=expr_array_replace(axiom[3],key,substituter)
               update_axioms.append(axiom)
            else:
               update_axioms.append(axiom)
    return update_axioms



#normal infix printing
def expr2stringSimplify(e):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        return op
    else:
        if op=='and' or op=='or':
            if len(args)==1:
                return expr2stringSimplify(args[0])
            else:
                return '('+(' '+op+' ').join(list(expr2stringSimplify(x) for x in args))+')'
        elif op=='not' and len(args)==1:
            return 'not '+expr2stringSimplify(args[0])
        elif op=='implies' and len(args)==2:
            return expr2stringSimplify(args[0])+ ' -> '+expr2stringSimplify(args[1])
        elif op in _infix_op and len(args)==2:
            return '(' + expr2stringSimplify(args[0])+ op+expr2stringSimplify(args[1])+')'
        else:
            if op is 'ite':
               expresion1 = expr2stringSimplify(args[1])
               expresion2 =  expr2stringSimplify(args[2])
               if ('and' not in expresion1 and 'or' not in expresion1 and 'ite' not in expresion1) and ('and' not in expresion2 and 'or' not in expresion2 and 'ite' not in expresion2) and simplify(expresion1+'=='+expresion2)==True:
                  return expresion1
               else:
                  return op +'('+ ','.join(list(expr2stringSimplify(x) for x in args))+ ')'
            else:
               return op +'('+ ','.join(list(expr2stringSimplify(x) for x in args))+ ')'


# expr_replace(e,e1,e2): replace all subterm e1 in e by e2

#e=['a', ['implies', ['<', ['_n1'], ['_N1']], ['<', ['x2', ['_n1']], ['y2', ['_n1']]]]]

#e=['a', ['<', ['x2', ['_N1']], ['y2', ['_N1']]]]

def expr_complement(e): #e,e1,e2: expres
    if e[:1]==['<']:
    	e[:1]=['>=']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['>']:
    	e[:1]=['<=']
    	return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['>=']:
        e[:1]=['<']
        return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['<=']:
        e[:1]=['>']
        return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['==']:
        e[:1]=['!=']
        return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['!=']:
        e[:1]=['==']
        return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['&&']:
        e[:1]=['||']
        return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['||']:
        e[:1]=['&&']
        return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['and']:
        e[:1]=['or']
        return e[:1]+list(expr_complement(x) for x in expr_args(e))
    elif e[:1]==['or']:
        e[:1]=['and']
        return e[:1]+list(expr_complement(x) for x in expr_args(e))
    else:
        return e[:1]+list(expr_complement(x) for x in expr_args(e))


"""
Convert Inequality to Normal Form

"""


def normal_form_constant(expression, constant):
    #print "*************"
    #print expression
    #print "*************"
    mult_by_minus_one_map = {
    	None: '==',
    	'>=': '<=',
    	'<=': '>=',
    	'>': '<',
    	'<': '>',
	}
    ineq=simplify(expression)
    l = ineq.lhs
    r = ineq.rhs
    op = ineq.rel_op
    all_on_left = l - r
    coeff_dict = all_on_left.as_coefficients_dict()
    var_types = coeff_dict.keys()
    new_rhs = sympify(0)
    for s in var_types:
    	if s != simplify(constant):
           factor=s.coeff(simplify(constant))
           if factor==0:
              all_on_left = (all_on_left - (coeff_dict[s]*s))
              new_rhs = (new_rhs - (coeff_dict[s]*s))
    all_on_left=all_on_left.expand(basic=True)
    coeff_dict = all_on_left.as_coefficients_dict()
    var_types = coeff_dict.keys()
    if len(var_types)==1:
    	for s in var_types:
            if coeff_dict[s]<0:
               all_on_left = all_on_left * -1
               new_rhs = new_rhs * -1
               op = mult_by_minus_one_map[op]	
    	factor=all_on_left.coeff(simplify(constant))
    	if factor!=0:
           all_on_left=all_on_left/factor
           new_rhs=new_rhs/factor
    else:
    	all_on_left=simplify(all_on_left)
    	new_rhs=simplify(new_rhs)
    	coeff_dict = all_on_left.as_coefficients_dict()
    	var_types = coeff_dict.keys()
    	if len(var_types)==1:
           for s in var_types:
               if coeff_dict[s]<0:
                  all_on_left = all_on_left * -1
                  new_rhs = new_rhs * -1
                  op = mult_by_minus_one_map[op]	
    
    #print "*************"
    #print all_on_left
    #print new_rhs
    #print "*************"
    return Relational(all_on_left,new_rhs,op)


#wff to Simplified Expression
def expr2simplified(e,flag):
    args=expr_args(e)
    op=expr_op(e)
    if len(args)==0:
        return op,flag
    else:
        if op in _infix_op and len(args)==2:
            expr1,flag=expr2simplified(args[0],flag)
            if flag==True:
                expr2,flag=expr2simplified(args[1],flag)
                flag=True
            else:
                expr2,flag=expr2simplified(args[1],flag)
            if op=='*' and expr_op(args[0])=='/':
               n,d=fraction(expr1)
               if gcd(d,expr2)!=1:
                  flag=True
            elif op=='/' and expr_op(args[0])=='*':
	            n,d=fraction(expr2)
	            if gcd(expr1,d)!=1:
	                flag=True
            if flag==True:
               expression= '(' + expr1+ op + expr2 +')' 
            else:
                expression= '((' + str(pow_to_mul(powsimp(expr1)))+ ')'+ op + '('+ str(pow_to_mul(powsimp(expr2)))+'))' 
            return expression,flag
        else:
            return op +'('+ ','.join(list(trim_p(expr2string1(x)) for x in args))+ ')',flag

def organizeFreeVariable(f,o,a,vfacts):
    struct_type_list=[]
    for vfact in vfacts.keys():
        info_list=vfacts[vfact]
        for info in info_list:
            if len(info_list[info])>0 and info_list[info][1] not in ['int','short','unsigned','long','char','float','double','array']:
                struct_type_list.append(info)
    
    for x in o:
        e=o[x]
        if  e[0]=='e':
            if is_Stuct(e[-2][0],struct_type_list):
                e[-1] = expr_replace(e[-1],eval("['_x1']"),eval("['_s1']"))
                e[-2] = expr_replace(e[-2],eval("['_x1']"),eval("['_s1']"))
    
    for e in a:
        if e[0]=='i1' or e[0]=='i0':
            if is_Stuct(e[-2][0],struct_type_list):
                e[-1] = expr_replace(e[-1],eval("['_x1']"),eval("['_s1']"))
                e[-2] = expr_replace(e[-2],eval("['_x1']"),eval("['_s1']"))

def is_Stuct(var,struct_type_list):
    status=False
    for x in struct_type_list:
        temp=var.replace(x,'').strip()
        if is_number(temp)==True:
            status=True
    return status




#Test Case 1
#variable="d1array4"

#Test Case 2
#variable="d1ar4"	
	
def isArrayFunction( variable ):
	status=False
	find=regex.compile(r'([d]\d[a][r][r][a][y]\d|[d]\d[a][r][r][a][y])')
	group = find.search(variable)
	if group is not None:
		status=True
	return status





