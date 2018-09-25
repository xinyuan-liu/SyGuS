from z3 import *

verbose=False


def DeclareVar(sort,name):
    if sort=="Int":
        return Int(name)

def getSort(sort):
    if sort=="Int":
        return IntSort()

def toString(Expr,Bracket=True):
    subexpr=[]
    for expr in Expr:
        if type(expr)==list:
            subexpr.append(toString(expr))
        else:
            subexpr.append(expr)

    if not Bracket:
        return "%s"%(' '.join(subexpr))
    # Avoid Redundant Brackets
    if type(Expr)==list and len(Expr)==1:
        return "%s"%(' '.join(subexpr))
    else:
        return "(%s)"%(' '.join(subexpr))

def GenSpecConn(Expr,SpecConnSet,synFunction):
    for expr in Expr:
        if type(expr)==list:
            if expr[0]==synFunction.name:
                assert(len(expr)-1==len(synFunction.argList))
                l=[]
                for xpr in expr[1:]:
                    l.append(toString(xpr,False))
                SpecConnSet.add(tuple(l))
                for xpr in expr[1:]:
                    GenSpecConn(xpr,SpecConnSet,synFunction)
            else:
                GenSpecConn(expr,SpecConnSet,synFunction)

def ReadQuery(bmExpr):
    SynFunExpr=[]
    VarDecMap={}
    Constraints=[]
    FunDefMap={}
    for expr in bmExpr:
        if len(expr)==0:
            continue
        elif expr[0]=='synth-fun':
            SynFunExpr=expr
        elif expr[0]=='declare-var':
            VarDecMap[expr[1]]=expr
        elif expr[0]=='constraint':
            Constraints.append(expr)
        elif expr[0]=='define-fun':
            FunDefMap[expr[1]]=expr
    
    if verbose:
        print(SynFunExpr)
        print(VarDecMap)
        print(FunDefMap)
        print(Constraints)
    
    VarTable={}
    # Declare Var
    for var in VarDecMap:
        VarTable[var]=DeclareVar(VarDecMap[var][2],var)

    # Declare Target Function
    class SynFunction:
        def __init__(self, SynFunExpr):
            self.name=SynFunExpr[1]
            # TODO: single arg
            self.argList=SynFunExpr[2]
            self.retSort=SynFunExpr[3]
            self.Sorts=[]
            for expr in self.argList:
                self.Sorts.append(getSort(expr[1]))
            self.Sorts.append(getSort(self.retSort))
    synFunction=SynFunction(SynFunExpr)
    targetFunction=Function('__TARGET_FUNCTION__', *(synFunction.Sorts))
    
    #Specification
    spec=[]
    spec_smt2=[]
    for constraint in Constraints:
        spec_smt2.append('(assert %s)'%(toString(constraint[1:])))
    spec_smt2='\n'.join(spec_smt2)
    spec = parse_smt2_string(spec_smt2,decls=dict(VarTable, **{synFunction.name:targetFunction}))
    spec = And(spec)
    if verbose:
        print("spec:",spec)
    
    #Input Port Specification
    InputPortList=[]
    for i in range(len(synFunction.argList)):
        arg=synFunction.argList[i]
        portName="__INPUT__PORT__%d__"%i
        InputPortList.append((portName,DeclareVar(arg[1],portName)))
    if verbose:
        print(InputPortList)

    SpecConnSet=set()
    
    for constraint in Constraints:
        GenSpecConn(constraint[1:],SpecConnSet,synFunction)
    if verbose:
        print(SpecConnSet)
    SpecConnSet=list(SpecConnSet)
    SpecConn=[]
    for SpecConnExpr in SpecConnSet:
        spec_smt2=[]
        for i in range(len(SpecConnExpr)):
            spec_smt2.append('(assert (= %s __INPUT__PORT__%d__))'%(SpecConnExpr[i],i))
        spec_smt2='\n'.join(spec_smt2)
        specConn=parse_smt2_string(spec_smt2,decls=dict(VarTable.items()+InputPortList+[(synFunction.name,targetFunction)]))
        SpecConn.append(And(specConn))
    specConn=Or(SpecConn)
    if verbose:
        print(specConn)

    class Checker:
        def __init__(self, spec, specConn, VarTable, InputPortList, targetFunction, synFunction):
            self.spec=spec
            self.specConn=specConn
            self.VarTable=VarTable
            self.InputPortList=InputPortList
            self.targetFunction=targetFunction
            self.synFunction=synFunction
            argString=[]
            for item in InputPortList:
                argString.append(item[0])
            argString=' '.join(argString)
            self.appendAssert="(assert (= (__TARGET_FUNCTION__ %s) (%s %s)))"%(argString,synFunction.name,argString)
            self.SymbolTable=dict(InputPortList+[("__TARGET_FUNCTION__",targetFunction)])
            self.solver=Solver()

        def check(self,funcDefStr):
            self.solver.push()
            self.solver.add(Not(self.spec))
            self.solver.add(self.specConn)
            constraint=parse_smt2_string(funcDefStr+self.appendAssert,decls=self.SymbolTable)
            self.solver.add(constraint)
            res=self.solver.check()
            if res==unsat:
                self.solver.pop()
                return None
            else:
                model=self.solver.model()
                self.solver.pop()
                counterExample=[]
                for item in InputPortList:
                    counterExample.append(model[item[1]])
                return counterExample
    
    checker=Checker(spec, specConn, VarTable, InputPortList, targetFunction, synFunction)
    return checker