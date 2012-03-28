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
     findCriticalPair (r4) (r2) ([]) == [Axiom (Var "v0",Func "+" [Func "-" [Func "-" [Var "v0"]],Func "0" []])] ]

groupAxioms = 
    [Axiom (Func "+" [Func "0" [],Var "x"],Var "x"),
            Axiom (Func "+" [Func "-" [Var "x"],Var "x"],Func "0" []),
            Axiom (Func "+" [Func "+" [Var "x",Var "y"],Var "z"],Func "+" [Var "x",Func "+" [Var "y",Var "z"]])]

strangeAxioms =
    [Axiom (Func "*" [Func "e" [],Var "x"],Var "x"),
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
r6 =  ReductionRule (Func "+" [Func "-" [Func "-" [Var "v0"]],Func "0" []],Var "v0")
r7 =  ReductionRule (Func "+" [Func "-" [Func "-" [Var "v0"]],Var "v1"],Func "+" [Var "v0",Var "v1"])
r8 =  ReductionRule (Func "+" [Var "v0",Func "0" []],Var "v0")
r9 =  ReductionRule (Func "-" [Func "0" []],Func "0" [])
r10 =  ReductionRule (Func "-" [Func "-" [Var "v0"]],Var "v0")
r11 =  ReductionRule (Func "+" [Var "v0",Func "-" [Var "v0"]],Func "0" [])
r12 =  ReductionRule (Func "+" [Var "v0",Func "+" [Func "-" [Var "v0"],Var "v1"]],Var "v1")
r13 =  ReductionRule (Func "+" [Var "v0",Func "+" [Var "v1",Func "-" [Func "+" [Var "v0",Var "v1"]]]],Func "0" [])
r14 =  ReductionRule (Func "+" [Var "v0",Func "-"[Func "+" [Var "v0",Var "v1"]]],Var "v1")
r15 =  ReductionRule (Func "-" [Func "+" [Var "v0",Var "v1"]],Func "+" [Func "-" [Var "v0"],Func "-" [Var "v1"]])
allRules = [r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15]

y n = (apply kb n) (groupAxioms,[])

debugKB :: ([Axiom] , [ReductionRule]) -> ([Axiom],[ReductionRule])
debugKB ([],rules) = ([],rules)
debugKB (axioms,rules) = 
      if orderTerms (lhs normalisedAxiom) (rhs normalisedAxiom) /= EQ
        then 
            (superposeRules rule newRules restAxioms,newRules)
        else debugKB (restAxioms, rules)
      where (axiom,restAxioms) = takeAxiom axioms; 
            normalisedAxiom = normaliseAxiom axiom rules; 
            rule = renameVarsInReductionRuleWithPrefix "" (orderAxiom normalisedAxiom)
            newRules = rules++[rule]

result :: Int -> ([Axiom],[ReductionRule])
result 0 = (groupAxioms,[])
result n = debugKB (result (n-1))

printResult n = do
    printAxioms a
    printRules r
    where (a,r) = result n

printList [] = return () 
printList (x:xs) =
   print x >> printList xs

printRules rules = printList rules
printAxioms axioms = printList axioms

resultRules :: Int -> [ReductionRule]
resultRules n = snd $ result n
resultAxioms :: Int -> [Axiom]
resultAxioms n = fst $ result n
normaliseResultAxioms n = 
   map (\x-> normaliseAxiom x $ resultRules n) $ resultAxioms n

printResultNewAxioms n = 
    printAxioms $ (superposeRules (head $ reverse $ resultRules n) (resultRules n) $ [])

getRules (ReductionRules rules) = rules
getRule (ReductionRule (rule,_)) = rule


bfindCriticalPair :: ReductionRule -> ReductionRule -> Axioms -> Axioms
bfindCriticalPair ruleA ruleB axioms=
    find ruleB ruleA $ find ruleA ruleB axioms
    where
    find :: ReductionRule -> ReductionRule -> Axioms -> Axioms
    find (ReductionRule (termA,resultA)) (ReductionRule (termB,resultB)) axioms =
        if bcheckCriticalPair renamedTermA renamedTermB
          then baddCriticalPair (ReductionRule (renamedTermA,renamedResultA)) (ReductionRule (renamedTermB,renamedResultB)) axioms
          else axioms
      where (ReductionRule (renamedTermA,renamedResultA)) = renameVarsInReductionRuleWithPrefix "l" (ReductionRule (termA,resultA))
            (ReductionRule (renamedTermB,renamedResultB)) = renameVarsInReductionRuleWithPrefix "r" (ReductionRule (termB,resultB))

baddCriticalPair :: ReductionRule -> ReductionRule -> Axioms -> Axioms
baddCriticalPair ruleA ruleB (Axioms axioms) = 
    add ruleA ruleB (Axioms axioms) (createCriticalPair ruleA ruleB)
    where
    add :: ReductionRule -> ReductionRule -> Axioms -> Maybe Axiom -> Axioms
    add ruleA ruleB (Axioms axioms) (Nothing) = (Axioms axioms) 
    add ruleA ruleB (Axioms axioms) (Just axiom) = 
      if not (elem axiom axioms)
        then (Axioms (axioms++[axiom]))
        else (Axioms axioms)

bcheckCriticalPair :: Term -> Term -> Bool 
bcheckCriticalPair (Func nameA argsA) (Func nameB argsB) =
    if orderTerms (Func nameA argsA) (Func nameB argsB) == EQ
      then
         any (\a -> bcheckSuperposition a (Func nameB argsB)) argsA
      else
        if bcheckSuperposition (Func nameA argsA) (Func nameB argsB) 
          then True
          else any (\a -> bcheckCriticalPair a (Func nameB argsB)) argsA
bcheckCriticalPair _ _ = False 


bcheckSuperposition :: Term -> Term -> Bool
bcheckSuperposition (Func nameA argsA) (Func nameB argsB) =  
    if bcheckStructure (Func nameA argsA) (Func nameB argsB) 
      then bcheckBindedVars $ fixBindedVars (listBindedVars (ReductionRule (Func nameA argsA,Func nameA argsA)) (Func nameB argsB))
      else False
bcheckSuperposition _ _ = False 
bcheckStructure :: Term -> Term -> Bool --propably ready
bcheckStructure (Var aV) (Func bName bArgs) = True --ok
bcheckStructure (Var aV) (Var bV) = True --ok
--bcheckStructure (Func aName aArgs) (Var bV) = True--False --propably  na dole chyba działa
bcheckStructure (Func aName (a:aArgs)) (Var bV) = False --True --propably! False
bcheckStructure (Func aName []) (Var bV) = True --False --propably! True
bcheckStructure (Func aName aArgs) (Func bName bArgs) = -- ok
      if aName == bName && length aArgs == length bArgs
        then (all (uncurry bcheckStructure) (zip aArgs bArgs) || all (uncurry bcheckStructure) (zip bArgs aArgs))
        else False
--wrong!
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



betterCreateCriticalTerm :: Term -> Term -> Maybe Term
betterCreateCriticalTerm (Func nameA argsA) (Func nameB argsB) = 
    create (Func nameA argsA) (Func nameB argsB) (Func nameA argsA)
    where
    create :: Term -> Term -> Term -> Maybe Term
    create (Func nameA argsA) (Func nameB argsB) result = 
      if orderTerms (Func nameA argsA) (Func nameB argsB) == EQ
        then 
          betterSuperposeArgs argsA (Func nameB argsB) result
        else
          if betterCheckSuperposition (Func nameA argsA) (Func nameB argsB) 
            then
              betterSuperpose (Func nameA argsA) (Func nameB argsB) result
            else
              betterSuperposeArgs argsA (Func nameB argsB) result

betterSuperpose :: Term -> Term -> Term -> Maybe Term
betterSuperpose termA termB termResult = --Just termA
    Just $ bindingAtoB (fixedBindingBtoA (fixedBindingAtoB (termResult)))
    where 
    bindingAtoB :: Term -> Term
    bindingAtoB term = foldl (changeBinding) term (listBindedVars (ReductionRule (termA,termA)) termB) 
    bindingBtoA :: Term -> Term
    bindingBtoA term = foldl (changeBinding) term (listBindedVars (ReductionRule (termB,termB)) termA) 
    fixedBindingAtoB :: Term -> Term
    fixedBindingAtoB term = foldl (changeBinding) term (betterFix $ listBindedVars (ReductionRule (termA,termA)) termB) 
    fixedBindingBtoA :: Term -> Term
    fixedBindingBtoA term = foldl (changeBinding) term (betterFix $ listBindedVars (ReductionRule (termB,termB)) termA) 


betterFix :: [(Term,Term)] -> [(Term,Term)]
betterFix ((Var a,Var b):rest) = betterFix rest
betterFix ((Var v,Func name args):rest) = (Var v,Func name args):(betterFix rest)
betterFix [] = []

betterSuperposeArgs :: [Term] -> Term -> Term -> Maybe Term 
betterSuperposeArgs ((Func nameA argsA):terms) termB termResult = 
    if betterCheckSuperposition (Func nameA argsA) termB
      then 
        betterSuperpose (Func nameA argsA) termB termResult
      else
        betterSuperposeArgs (terms++argsA) termB termResult
betterSuperposeArgs ((Var a):terms) termB termResult = 
    betterSuperposeArgs terms termB termResult
betterSuperposeArgs [] termB termResult = Nothing

betterCheckSuperposition  = bcheckSuperposition 
