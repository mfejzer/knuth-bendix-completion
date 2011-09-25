import KnuthBendixCompletion

runTests :: Bool
runTests = all [
--reduceTerm (ReductionRule (translate "f x (f x y)",translate "g x")) (translate "a (f (f g h)) e")
(checkRuleInTerm (ReductionRule (translate "f x x",translate "g x")) (translate "f (L kloc) (L kloc)") == True)
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
Func "a" [Func "g" [Func "L" [Var "kloc"]],Func "f" [Var "e",Var "e"]])),
reduce (ReductionRules [(ReductionRule (translate "f x x",translate "g x"))]) (translate "a (f (L kloc) (L kloc)) (f e e)") ==(
Func "a" [Func "g" [Func "L" [Var "kloc"]],Func "f" [Var "e",Var "e"]])

]

