module Test where
import KnuthBendixCompletion

runTests = and [reduceTerm (ReductionRule (translate "f x (f x y)",translate "g x")) (translate "a (f (f g h)) e") == (Func "a" [Func "f" [Func "f" [Var "g",Var "h"]],Var "e"])
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
             ,(reduce (ReductionRules [(ReductionRule (translate "f x x",translate "g x"))]) (translate "a (f (L kloc) (L kloc)) (f e e)") ==(
               Func "a" [Func "g" [Func "L" [Var "kloc"]],Func "f" [Var "e",Var "e"]]))
             ,(renameVars (translate "a (f (f g h)) e") == (Func "a" [Func "f" [Func "f" [Var "v0",Var "v1"]],Var "v2"]))
             ,(renameVarsWithPrefix "prefix" (translate "a (f (f g h)) e") == (Func "a" [Func "f" [Func "f" [Var "prefixv0",Var "prefixv1"]],Var "prefixv2"]))
             ,(reduce (ReductionRules [(ReductionRule (Func "f" [Var "v0",Func "f" [Var "v0",Var "v1"]],Func "g" [Var "v0"]))]) (translate "f a (f a b)") ==(Func "g" [Var "a"]))
             ,(reduce (ReductionRules [(ReductionRule (Func "f" [Var "v0",Func "f" [Var "v0",Var "v1"]],Func "g" [Var "v0"]))]) (translate "f a (f b a)") == 
               (Func "f" [Var "a",Func "f" [Var "b",Var "a"]]))
             ,(renameVarsInReductionRule (ReductionRule (translate "f x (f x y)",translate "g x")) == 
               (ReductionRule (Func "f" [Var "v0",Func "f" [Var "v0",Var "v1"]],Func "g" [Var "v0"])))
             ,checkCriticalPair (translate "+ z") (translate "(+ x)") == True
             ,checkCriticalPair (translate "+ (+ x y) z") (translate "+ (- x) x") == True
             ,checkSuperposition  (translate "+ x y") (translate "+ (- x) x") == True
             ,checkSuperposition  (translate "+ x (- y)") (translate "+ (- x) x") == False
             ,superpose (translate "+ x y") (translate "+ (- x) x") (translate "+ x y") == Func "+" [Func "-" [Var "x"],Var "x"]
             ,createCriticalTerm  (translate "+ (+ x y) z") (translate "+ (- x) x") ==Func "+" [Func "+" [Func "-" [Var "x"],Var "x"],Var "z"]
             ,(createCriticalPair (ReductionRule (translate "+ (+ x y) z",translate "+ x (+ y z)")) (ReductionRule (translate "+ (- x) x",Func "zero" []))) ==
               Axiom (Func "+" [Func "-" [Var "v0"],Func "+" [Var "v0",Var "v1"]],Func "+" [Func "zero" [],Var "v1"])
             ,findCriticalPair (ReductionRule (translate "+ (+ x y) z",translate "+ x (+ y z)")) (ReductionRule (translate "+ (- x) x",Func "zero" [])) (Axioms []) ==
               Axioms [Axiom (Func "+" [Func "-" [Var "v0"],Func "+" [Var "v0",Var "v1"]],Func "+" [Func "zero" [],Var "v1"])]
             ,orderAxiom (createCriticalPair (ReductionRule (translate "+ (+ x y) z",translate "+ x (+ y z)")) (ReductionRule (translate "+ (- x) x",Func "zero" []))) ==
               ReductionRule (Func "+" [Func "-" [Var "v0"],Func "+" [Var "v0",Var "v1"]],Func "+" [Func "zero" [],Var "v1"])
             ]

groupAxioms = 
    Axioms [Axiom (Func "+" [Func "0" [],Var "x"],Var "x"),
            Axiom (Func "+" [Func "-" [Var "x"],Var "x"],Func "0" []),
            Axiom (Func "+" [Func "+" [Var "x",Var "y"],Var "z"],Func "+" [Var "x",Func "+" [Var "y",Var "z"]])]

strangeAxioms =
    Axioms [Axiom (Func "*" [Func "e" [],Var "x"],Var "x"),
            Axiom (Func "*" [Var "x",Func "e" []],Var "x"),
            Axiom (Func "*" [Var "x", Var "x"],Func "e" []),
            Axiom (Func "*" [Func "*" [Var "x",Var "y"],Var "z"],Func "*" [Var "x",Func "*" [Var "y",Var "z"]])] 


rules =
  (ReductionRules [r0,r1,r2,r3])
r0 =  ReductionRule (Func "+" [Func "0" [],Var "x"],Var "x")
r1 =  ReductionRule (Func "+" [Func "-" [Var "x"],Var "x"],Func "0" [])
r2 =  ReductionRule (Func "+" [Func "+" [Var "x",Var "y"],Var "z"],Func "+" [Var "x",Func "+" [Var "y",Var "z"]])
r3 =  ReductionRule (Func "+" [Func "-" [Var "v0"],Func "+" [Var "v0",Var "v1"]],Var "v1")


testFindCriticalPairR2R3 = 
   findCriticalPair r2 r3 (Axioms []) == 
     (Axioms [Axiom (Func "+" [Func "-" [Var "v0"],Func "+" [Func "+" [Var "v0",Var "v1"],Var "v2"]],Func "+" [Var "v1",Var "v2"])])


