import sys
import sexp
import pprint
import translator

def stripComments(bmFile):
    noComments = '('
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + ')'


if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0]
    pprint.pprint(bmExpr)
    checker=translator.ReadQuery(bmExpr)
    
    print (checker.check('(define-fun max2 ((x Int) (y Int)) Int x)'))
    print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (+ x y))'))
    print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) y x))'))
