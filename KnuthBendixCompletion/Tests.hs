module KnuthBendixCompletion.Tests where
import KnuthBendixCompletion.Algorithm
import KnuthBendixCompletion.Datatypes
import Parser

runTests = and tests
tests = [reduceTerm (ReductionRule (translate "f x (f x y)",translate "g x")) (translate "a (f (f g h)) e") == (Func "a" [Func "f" [Func "f" [Var "g",Var "h"]],Var "e"])
             ,(checkRuleInTerm (ReductionRule (translate "f x x",translate "g x")) (translate "f (L kloc) (L kloc)") == True)
             ,(listBindedVars  (ReductionRule (translate "f x x",translate "g x")) (translate "f e g") == [(Var "x",Var "e"),(Var "x",Var "g")])
             ,(reduceTerm (ReductionRule (translate "f x (f x y)",translate "g x")) (translate "a (f e (f e h))") == (Func "a" [Func "g" [Var "e"]]))
             ,(reduceTerm (ReductionRule (translate "f x (f x y)",translate "g y")) (translate "a (f e (f e h))") == (Func "a" [Func "g" [Var "h"]]))
             ,(reduceTerm   (ReductionRule (translate "f x x",translate "g x x")) (translate "a (f (L kloc) (L kloc)) (f e e)") == (
               Func "a" [Func "g" [Func "L" [Var "kloc"],Func "L" [Var "kloc"]],Func "f" [Var "e",Var "e"]]))
             ,(reduceTerm   (ReductionRule (translate "f x x",translate "g x x")) (translate "a (f (L kloc) (o kloc)) (f e e)") == (
               Func "a" [Func "f" [Func "L" [Var "kloc"],Func "o" [Var "kloc"]],Func "g" [Var "e",Var "e"]]))
             ,(reduceTerm   (ReductionRule (translate "f x x",translate "g x")) (translate "a (f (L kloc) (o kloc)) (f e e)") == (
               Func "a" [Func "f" [Func "L" [Var "kloc"],Func "o" [Var "kloc"]],Func "g" [Var "e"]]))
             ,(reduceTerm   (ReductionRule (translate "f x x",translate "g x")) (translate "a (f (L kloc) (L kloc)) (f e e)") == ( 
               Func "a" [Func "g" [Func "L" [Var "kloc"]],Func "f" [Var "e",Var "e"]]))
             ,(reduce ([(ReductionRule (translate "f x x",translate "g x"))]) (translate "a (f (L kloc) (L kloc)) (f e e)") ==(
               Func "a" [Func "g" [Func "L" [Var "kloc"]],Func "f" [Var "e",Var "e"]]))
             ,(renameVars (translate "a (f (f g h)) e") == (Func "a" [Func "f" [Func "f" [Var "v0",Var "v1"]],Var "v2"]))
             ,(renameVarsWithPrefix "prefix" (translate "a (f (f g h)) e") == (Func "a" [Func "f" [Func "f" [Var "prefixv0",Var "prefixv1"]],Var "prefixv2"]))
             ,(reduce ([(ReductionRule (Func "f" [Var "v0",Func "f" [Var "v0",Var "v1"]],Func "g" [Var "v0"]))]) (translate "f a (f a b)") ==(Func "g" [Var "a"]))
             ,(reduce ([(ReductionRule (Func "f" [Var "v0",Func "f" [Var "v0",Var "v1"]],Func "g" [Var "v0"]))]) (translate "f a (f b a)") == 
               (Func "f" [Var "a",Func "f" [Var "b",Var "a"]]))
             ,(renameVarsInReductionRule (ReductionRule (translate "f x (f x y)",translate "g x")) == 
               (ReductionRule (Func "f" [Var "v0",Func "f" [Var "v0",Var "v1"]],Func "g" [Var "v0"])))
             ,checkCriticalPair (translate "+ z") (translate "(+ x)") == True
             ,checkCriticalPair (translate "+ (+ x y) z") (translate "+ (- x) x") == True
             ,checkSuperposition  (translate "+ x y") (translate "+ (- x) x") == True
             ,checkSuperposition  (translate "+ x (- y)") (translate "+ (- x) x") == False
--             ,superpose (translate "+ x y") (translate "+ (- x) x") (translate "+ x y") == Func "+" [Func "-" [Var "x"],Var "x"]
--             ,createCriticalTerm  (translate "+ (+ x y) z") (translate "+ (- x) x") ==Func "+" [Func "+" [Func "-" [Var "x"],Var "x"],Var "z"]
--             ,(createCriticalPair (ReductionRule (translate "+ (+ x y) z",translate "+ x (+ y z)")) (ReductionRule (translate "+ (- x) x",Func "zero" []))) ==
--               Axiom (Func "+" [Func "-" [Var "v0"],Func "+" [Var "v0",Var "v1"]],Func "+" [Func "zero" [],Var "v1"])
--             ,findCriticalPair (ReductionRule (translate "+ (+ x y) z",translate "+ x (+ y z)")) (ReductionRule (translate "+ (- x) x",Func "zero" [])) (Axioms []) ==
--               Axioms [Axiom (Func "+" [Func "-" [Var "v0"],Func "+" [Var "v0",Var "v1"]],Func "+" [Func "zero" [],Var "v1"])]
--             ,orderAxiom (createCriticalPair (ReductionRule (translate "+ (+ x y) z",translate "+ x (+ y z)")) (ReductionRule (translate "+ (- x) x",Func "zero" []))) ==
--               ReductionRule (Func "+" [Func "-" [Var "v0"],Func "+" [Var "v0",Var "v1"]],Func "+" [Func "zero" [],Var "v1"])
--             ,findCriticalPair r3 r3 (Axioms []) == 
--               Axioms [Axiom (Func "+" [Var "v0",Var "v1"],Func "+" [Func "-" [Func "-" [Var "v0"]],Var "v1"])]
             ]

runReductionTests = and reductionTests
reductionTests = 
   [ findCriticalPair (r3) (r2) ([]) == [Axiom (Func "+" [Func "-" [Var "v0"],Func "+" [Var "v0",Var "v1"]],Func "+" [Func "0" [],Var "v1"])],
     findCriticalPair (r4) (r1) ([]) == [Axiom (Var "v0",Func "+" [Func "-" [Func "0" []],Var "v0"])],
     findCriticalPair (r4) (r2) ([]) == [Axiom (Var "v0",Func "+" [Func "-" [Func "-" [Var "v0"]],Func "0" []])],
     findCriticalPair (r4) (r4) ([]) == [Axiom (Func "+" [Var "v0",Var "v1"],Func "+" [Func "-" [Func "-" [Var "v0"]],Var "v1"])],
     findCriticalPair r8 r2 [] == [Axiom (Func "-" [Func "0" []], Func "0" []),
                                   Axiom (Func "0" [], Func "-" [Func "0" []])],
     findCriticalPair r8 r7 [] == [Axiom (Func "-" [Func "-" [Var "v0"]], Func "+" [Var "v0",Func "0" []]),
                                   Axiom (Func "+" [Var "v0",Func "0" []], Func "-" [Func "-" [Var "v0"]])],
     findCriticalPair r7 r2 [] == [Axiom (Func "0" [], Func "+" [Var "v0",Func "-" [Var "v0"]])],
     findCriticalPair r7 r4 [] == [Axiom (Func "+" [Var "v0",Func "+" [Func "-" [Var "v0"],Var "v1"]], Var "v1"),
                                   Axiom (Var "v1", Func "+" [Var "v0",Func "+" [Func "-" [Var "v0"],Var "v1"]])],
     findCriticalPair r3 r11 [] == [Axiom (Func "+" [Var "v0",Func "+" [Var "v0",Func "-" [Func "+" [Var "v0",Var "v0"]]]], Func "0" []),
                                    Axiom (Func "0" [], Func "+" [Var "v0",Func "+" [Var "v1",Func "-" [Func "+" [Var "v0",Var "v1"]]]])],
     findCriticalPair r4 r13 [] == [Axiom (Func "+" [Var "v1",Func "-" [Func "+" [Var "v0",Var "v1"]]],Func "+" [Func "-" [Var "v0"],Func "0" []]),
                                    Axiom (Func "0" [],Func "+" [Func "-" [Var "v0"],Func "+" [Func "+" [Var "v0",Var "v1"],Func "-" [Var "v1"]]])],
     findCriticalPair r4 r14 [] == [Axiom (Func "-" [Func "+" [Var "v0",Var "v1"]], Func "+" [Func "-" [Var "v0"],Func "-" [Var "v1"]])]
   ]


strangeAxioms =
    [Axiom (Func "*" [Func "e" [],Var "x"],Var "x"),
            Axiom (Func "*" [Var "x",Func "e" []],Var "x"),
            Axiom (Func "*" [Var "x", Var "x"],Func "e" []),
            Axiom (Func "*" [Func "*" [Var "x",Var "y"],Var "z"],Func "*" [Var "x",Func "*" [Var "y",Var "z"]])] 


rules = [r1,r2,r3,r4]
r1 =  ReductionRule (Func "+" [Func "0" [],Var "x"],Var "x")
r2 =  ReductionRule (Func "+" [Func "-" [Var "x"],Var "x"],Func "0" [])
r3 =  ReductionRule (Func "+" [Func "+" [Var "x",Var "y"],Var "z"],Func "+" [Var "x",Func "+" [Var "y",Var "z"]])
r4 =  ReductionRule (Func "+" [Func "-" [Var "v0"],Func "+" [Var "v0",Var "v1"]],Var "v1")
r5 =  ReductionRule (Func "+" [Func "-" [Func "0" []],Var "v0"],Var "v0")
r6 =  ReductionRule (Func "+" [Func "-" [Func "-" [Var "v0"]],Func "0" []],Var "v0")
r7 =  ReductionRule (Func "+" [Func "-" [Func "-" [Var "v0"]],Var "v1"],Func "+" [Var "v0",Var "v1"])
r8 =  ReductionRule (Func "+" [Var "v0",Func "0" []],Var "v0")
r9 =  ReductionRule (Func "-" [Func "0" []],Func "0" [])
r10 =  ReductionRule (Func "-" [Func "-" [Var "v0"]],Var "v0")
r11 =  ReductionRule (Func "+" [Var "v0",Func "-" [Var "v0"]],Func "0" [])
r12 =  ReductionRule (Func "+" [Var "v0",Func "+" [Func "-" [Var "v0"],Var "v1"]],Var "v1")
r13 =  ReductionRule (Func "+" [Var "v0",Func "+" [Var "v1",Func "-" [Func "+" [Var "v0",Var "v1"]]]],Func "0" [])
r14 =  ReductionRule (Func "+" [Var "v0",Func "-"[Func "+" [Var "v0",Var "v1"]]],Func "-" [Var "v1"])
r15 =  ReductionRule (Func "-" [Func "+" [Var "v0",Var "v1"]],Func "+" [Func "-" [Var "v0"],Func "-" [Var "v1"]])
allRules = [r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15]

apply f 1 e= f e
apply f n e= 
    case w of
      (Left a) -> Left a
      (Right ar) -> apply f (n-1) ar
    where w = f e

y n = (apply kb n) (groupAxioms,[])


