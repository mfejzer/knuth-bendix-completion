module Test where
import KnuthBendixCompletion

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
               ReductionRule (Func "+" [Func "-" [Var "v0"],Func "+" [Var "v0",Var "v1"]],Func "+" [Func "zero" [],Var "v1"]),
              findCriticalPair r3 r3 (Axioms []) == 
               Axioms [Axiom (Func "+" [Var "v0",Var "v1"],Func "+" [Func "-" [Func "-" [Var "v0"]],Var "v1"])]
             ]

runReductionTests = and reductionTests
reductionTests = 
   [ findCriticalPair (r3) (r2) (Axioms []) == Axioms [Axiom (Func "+" [Func "-" [Var "v0"],Func "+" [Var "v0",Var "v1"]],Func "+" [Func "0" [],Var "v1"])],
     findCriticalPair (r4) (r1) (Axioms []) == Axioms [Axiom (Var "v0",Func "+" [Func "-" [Func "0" []],Var "v0"])],
     findCriticalPair (r4) (r2) (Axioms []) == Axioms [Axiom (Var "v0",Func "+" [Func "-" [Func "-" [Var "v0"]],Func "0" []])] ]

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
  (ReductionRules [r1,r2,r3,r4])
r1 =  ReductionRule (Func "+" [Func "0" [],Var "x"],Var "x")
r2 =  ReductionRule (Func "+" [Func "-" [Var "x"],Var "x"],Func "0" [])
r3 =  ReductionRule (Func "+" [Func "+" [Var "x",Var "y"],Var "z"],Func "+" [Var "x",Func "+" [Var "y",Var "z"]])
r4 =  ReductionRule (Func "+" [Func "-" [Var "v0"],Func "+" [Var "v0",Var "v1"]],Var "v1")
r5 =  ReductionRule (Func "+" [Func "-" [Func "0" []],Var "v0"],Var "v0")
r6 =  ReductionRule (Func "+" [Func "-" [Func "-" [Var "v0"]],Func "0" []],Func "0" [])
r7 =  ReductionRule (Func "+" [Func "-" [Func "-" [Var "v0"]],Var "v1"],Func "+" [Var "v0",Var "v1"])
r8 =  ReductionRule (Func "+" [Var "v0",Func "0" []],Var "v0")
r9 =  ReductionRule (Func "-" [Func "0" []],Func "0" [])
r10 =  ReductionRule (Func "-" [Func "-" [Var "v0"]],Var "v0")
r11 =  ReductionRule (Func "+" [Var "v0",Func "-" [Var "v0"]],Func "0" [])
r12 =  ReductionRule (Func "+" [Var "x",Func "+" [Func "-" [Var "x"],Var "y"]],Var "y")
r13 =  ReductionRule (Func "+" [Var "v0",Func "+" [Var "v1",Func "-" [Func "+" [Var "v0",Var "v1"]]]],Func "0" [])
r14 =  ReductionRule (Func "+" [Var "v0",Func "-"[Func "+" [Var "v0",Var "v1"]]],Var "v1")
r15 =  ReductionRule (Func "-" [Func "+" [Var "v0",Var "v1"]],Func "+" [Func "-" [Var "v0"],Func "-" [Var "v1"]])

testFindCriticalPairR3R4 = 
   findCriticalPair r3 r4 (Axioms []) == 
     (Axioms [Axiom (Func "+" [Func "-" [Var "v0"],Func "+" [Func "+" [Var "v0",Var "v1"],Var "v2"]],Func "+" [Var "v1",Var "v2"])])

debugKB :: (Axioms , ReductionRules) -> (Axioms,ReductionRules)
debugKB (Axioms [],ReductionRules rules) = (Axioms [], ReductionRules rules)
debugKB (Axioms axioms,ReductionRules rules) = 
      if orderTerms (lhs normalisedAxiom) (rhs normalisedAxiom) /= EQ
        then 
--          ((foldl (superposeRulesOnAxioms (ReductionRules newRules)) restAxioms newRules),ReductionRules newRules)
            (superposeRules rule (ReductionRules newRules) restAxioms,ReductionRules newRules)
        else debugKB (restAxioms, ReductionRules rules)
      where (axiom,restAxioms) = takeAxiom (Axioms axioms); 
            normalisedAxiom = normaliseAxiom axiom (ReductionRules rules); 
            rule = renameVarsInReductionRuleWithPrefix "" (orderAxiom normalisedAxiom)
            newRules = rules++[rule]

result :: Int -> (Axioms,ReductionRules)
result 0 = (groupAxioms,ReductionRules [])
result (n+1) = debugKB (result n)

printResult n = do
    printAxioms a
    printRules r
    where (a,r) = result n

printList [] = return () 
printList (x:xs) =
   print x >> printList xs

printRules (ReductionRules rules) = printList rules
printAxioms (Axioms axioms) = printList axioms

resultRules :: Int -> ReductionRules
resultRules n = snd $ result n
resultAxioms :: Int -> Axioms
resultAxioms n = fst $ result n
normaliseResultAxioms n = 
   Axioms (map (\x-> normaliseAxiom x $ resultRules n) $ extractAxiom $ resultAxioms n) 
   where 
     extractAxiom (Axioms []) = []
     extractAxiom (Axioms (a:axioms)) = a: (extractAxiom (Axioms axioms))

printResultNewAxioms n = 
    printAxioms $ (superposeRules (head $ reverse $ extract $ resultRules n) (ReductionRules $ extract $ resultRules n) $ Axioms [])

extract (ReductionRules rules) = rules

--r7 = ReductionRule (Func "+" [Func "-" [Func "-" [Var "v0"]],Var "v1"],Func "+" [Var "v0",Var "v1"])

getRule (ReductionRule (rule,_)) = rule

buggyCriticalPairR7R2 = findCriticalPair r7 r2 (Axioms [])
buggyCriticalPairR2R7 = findCriticalPair r2 r7 (Axioms [])


bcheckCriticalPair :: Term -> Term -> Bool 
bcheckCriticalPair (Func nameA argsA) (Func nameB argsB) =
    if orderTerms (Func nameA argsA) (Func nameB argsB) == EQ
      then
         any (\a -> bcheckSuperposition a (Func nameB argsB)) argsA
      else
        if bcheckSuperposition (Func nameA argsA) (Func nameB argsB) 
          then True
          else any (\a -> bcheckSuperposition a (Func nameB argsB)) argsA
bcheckCriticalPair _ _ = False 


bcheckSuperposition :: Term -> Term -> Bool
bcheckSuperposition (Func nameA argsA) (Func nameB argsB) =  
    if bcheckStructure (Func nameA argsA) (Func nameB argsB) 
      then True --bcheckBindedVars (listBindedVars (ReductionRule (Func nameA argsA,Func nameA argsA)) (Func nameB argsB))
      else False
bcheckSuperposition _ _ = False 
bcheckStructure :: Term -> Term -> Bool --propably ready
bcheckStructure (Var aV) (Func bName bArgs) = True --ok
bcheckStructure (Var aV) (Var bV) = True --ok
bcheckStructure (Func aName aArgs) (Var bV) = True --False --propably
bcheckStructure (Func aName aArgs) (Func bName bArgs) = -- ok
      if aName == bName && length aArgs == length bArgs
        then all (uncurry bcheckStructure) (zip aArgs bArgs)
        else False
bcheckBindedVars :: [(Term,Term)] -> Bool
bcheckBindedVars [] = True
bcheckBindedVars ((Var v,term):rest) =
      if checkBindedVar (Var v,term) rest
        then bcheckBindedVars rest
        else False
      where
      checkBindedVar :: (Term,Term) -> [(Term,Term)] -> Bool
      checkBindedVar (Var v,bindedTerm) [] = True
      checkBindedVar (Var v,bindedTerm) ((Var h,hTerm):rest) =
        if v == h 
          then bindedTerm == hTerm && (checkBindedVar (Var v,bindedTerm) rest)
          else checkBindedVar (Var v,bindedTerm) rest

error = checkSuperposition  (getRule r7) (getRule r2)

