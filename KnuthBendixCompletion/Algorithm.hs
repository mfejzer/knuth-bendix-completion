module KnuthBendixCompletion.Algorithm where
import KnuthBendixCompletion.Datatypes
import Data.List (sort)

--ready
kbCompletion :: Axioms -> ReductionRules
kbCompletion axioms = kbc (axioms,[])
    where
    kbc ([],rules) = rules
    kbc (axioms,rules) = (kbc.kb) (axioms,rules)

apply g 1 = g
apply g n = g . (apply g (n-1))

kb :: ([Axiom],[ReductionRule]) -> ([Axiom],[ReductionRule])
kb ([],rules) = ([],rules)
kb (axioms,rules) = 
      if orderTerms (lhs normalisedAxiom) (rhs normalisedAxiom) /= EQ && (not $ elem rule rules)
        then 
          (superposeRules rule newRules restAxioms, newRules)
        else 
          (restAxioms,rules)
      where (axiom,restAxioms) = takeAxiom axioms;
            normalisedAxiom = normaliseAxiom axiom rules; 
            rule = renameVarsInReductionRuleWithPrefix "" (orderAxiom normalisedAxiom)
            newRules = makeNewRules rule rules


--simple, todo: complicated
takeAxiom :: [Axiom] -> (Axiom,[Axiom])
takeAxiom axioms = (head sortedAxioms, tail sortedAxioms)
    where
    sortedAxioms = axioms--List.sort axioms


makeNewRules :: ReductionRule -> [ReductionRule] -> [ReductionRule]
makeNewRules rule rules = mnr rule rules []
    where 
    mnr :: ReductionRule -> [ReductionRule] -> [ReductionRule] -> [ReductionRule]
    mnr rule [] acc = reverse $ (rule:acc)
    mnr rule (r:rules) acc = mnr rule rules $ add newRule acc
      where newRule = reduceRule rule r
            add :: (Maybe ReductionRule) -> [ReductionRule] -> [ReductionRule]
            add Nothing acc = acc
            add (Just rule) acc = if elem rule acc then acc else (rule:acc)

reduceRule :: ReductionRule -> ReductionRule -> Maybe ReductionRule
reduceRule reductingRule (ReductionRule (rule,result)) =
    if orderTerms reducedRule reducedResult /= EQ
      then
      if orderTerms reducedRule reducedResult /= LT
        then Just (ReductionRule (reducedRule,reducedResult))
        else Just (ReductionRule (reducedResult,reducedRule))
      else Nothing
    where reducedRule = reduceTerm reductingRule rule
          reducedResult = reduceTerm reductingRule result

normaliseAxiom :: Axiom -> [ReductionRule] -> Axiom
normaliseAxiom (Axiom (termA,termB)) rules = 
    (Axiom (reduceToNormalised rules termA,reduceToNormalised rules termB))

reduceToNormalised :: [ReductionRule] -> Term -> Term
reduceToNormalised rules term = 
    if orderTerms result term == EQ
      then term
      else reduceToNormalised rules result
    where result = reduce rules term

reduce :: [ReductionRule] -> Term -> Term
reduce [] term = term
reduce (rule:rest) term =
    if orderTerms result term == EQ
      then reduce rest term
      else result
    where result = reduceTerm renamedRule term
          renamedRule = renameVarsInReductionRuleWithPrefix "r" rule 

orderAxiom :: Axiom -> ReductionRule 
orderAxiom a = if orderTerms (lhs a) (rhs a) == GT then (ReductionRule (lhs a,rhs a)) else (ReductionRule (rhs a,lhs a))

orderTerms :: Term -> Term -> Ordering
orderTerms termA termB =
    if result == EQ 
      then checkVarCount termA termB
      else result 
    where
    result = order termA termB
    order :: Term -> Term -> Ordering
    order (Func name args) (Var v) = GT
    order (Var v) (Func name args) = LT
    order (Var a) (Var b) = EQ
    order (Func nameA (a:argsA)) (Func nameB (b:argsB)) =
        if result == EQ
          then order (Func nameA argsA) (Func nameB argsB)
          else result
        where result = order a b
    order (Func nameA []) (Func nameB []) = EQ
    order (Func nameA (a:args)) (Func nameB []) = GT
    order (Func nameA []) (Func nameB (b:args)) = LT
    checkVarCount :: Term -> Term -> Ordering
    checkVarCount termA termB =
       if (length.findVarsInTerm) termA > (length.findVarsInTerm) termB
         then GT
         else
           if (length.findVarsInTerm) termA < (length.findVarsInTerm) termB
             then LT
             else EQ


superposeRules :: ReductionRule -> [ReductionRule] -> [Axiom] -> [Axiom]
superposeRules rule [] axioms = axioms
superposeRules rule (r:rules) axioms =
    superposeRules rule rules newAxioms where
      newAxioms = findCriticalPair rule r axioms


findCriticalPair :: ReductionRule -> ReductionRule -> [Axiom] -> [Axiom]
findCriticalPair ruleA ruleB axioms =
    find ruleB ruleA $ find ruleA ruleB axioms
    where
    find :: ReductionRule -> ReductionRule -> [Axiom] -> [Axiom]
    find (ReductionRule (termA,resultA)) (ReductionRule (termB,resultB)) axioms =
        if checkCriticalPair renamedTermA renamedTermB
          then addCriticalPair (ReductionRule (renamedTermA,renamedResultA)) (ReductionRule (renamedTermB,renamedResultB)) axioms
          else axioms
      where (ReductionRule (renamedTermA,renamedResultA)) = renameVarsInReductionRuleWithPrefix "l" (ReductionRule (termA,resultA))
            (ReductionRule (renamedTermB,renamedResultB)) = renameVarsInReductionRuleWithPrefix "r" (ReductionRule (termB,resultB))


checkCriticalPair :: Term -> Term -> Bool 
checkCriticalPair (Func nameA argsA) (Func nameB argsB) =
    if orderTerms (Func nameA argsA) (Func nameB argsB) == EQ
      then
         any (\a -> checkSuperposition a (Func nameB argsB)) argsA
      else
        if checkSuperposition (Func nameA argsA) (Func nameB argsB) 
          then True
          else any (\a -> checkCriticalPair a (Func nameB argsB)) argsA
checkCriticalPair _ _ = False 


checkSuperposition :: Term -> Term -> Bool
checkSuperposition (Func nameA argsA) (Func nameB argsB) =  
    if checkStructure (Func nameA argsA) (Func nameB argsB) 
      then checkBindedVars $ fixBindedVars (listBindedVars (ReductionRule (Func nameA argsA,Func nameA argsA)) (Func nameB argsB))
      else False
    where
    checkStructure :: Term -> Term -> Bool 
    checkStructure (Var aV) (Func bName bArgs) = True 
    checkStructure (Var aV) (Var bV) = True 
    checkStructure (Func aName (a:aArgs)) (Var bV) = True --False --True --propably! False -> r6, r8; True -> r13
    checkStructure (Func aName []) (Var bV) = True --propably!
    checkStructure (Func aName aArgs) (Func bName bArgs) = 
      if aName == bName && length aArgs == length bArgs
        then all (uncurry checkStructure) (zip aArgs bArgs)
        else False
    checkBindedVars :: [(Term,Term)] -> Bool
    checkBindedVars [] = True
    checkBindedVars ((Var v,term):rest) =
      if checkBindedVar (Var v,term) rest
        then checkBindedVars rest
        else False
      where
      checkBindedVar :: (Term,Term) -> [(Term,Term)] -> Bool
      checkBindedVar (Var v,bindedTerm) [] = True
      checkBindedVar (Var v,bindedTerm) ((Var h,hTerm):rest) =
        if v == h 
          then bindedTerm == hTerm && (checkBindedVar (Var v,bindedTerm) rest)
          else checkBindedVar (Var v,bindedTerm) rest
checkSuperposition _ _ = False   

addCriticalPair :: ReductionRule -> ReductionRule -> [Axiom] -> [Axiom]
addCriticalPair ruleA ruleB axioms = 
    add axioms (createCriticalPair ruleA ruleB)
    where
    add :: [Axiom] -> [Axiom] -> [Axiom]
    add axioms [] = axioms
    add axioms (newAxiom:newAxioms) = 
      if not (elem newAxiom axioms)
        then add (axioms++[newAxiom]) newAxioms
        else add axioms newAxioms

createCriticalPair :: ReductionRule -> ReductionRule -> [Axiom]
createCriticalPair (ReductionRule (ruleA,resultA)) (ReductionRule (ruleB,resultB)) =
    createCritical (ReductionRule (ruleA,resultA)) (ReductionRule (ruleB,resultB)) (createCriticalTerm ruleA ruleB)
    where
    createCritical :: ReductionRule -> ReductionRule -> [Term] -> [Axiom]
    createCritical _ _ [] = []
    createCritical (ReductionRule (ruleA,resultA)) (ReductionRule (ruleB,resultB)) ((Func name args):rest) = 
      if orderTerms ruleA ruleB /= EQ
        then
          if (orderTerms (Func rname rargs) reductionA /= EQ && orderTerms (Func rname rargs) reductionB /= EQ ) 
            then (Axiom (reductionA,reductionB)):createRest
            else createRest
        else
          if (orderTerms (Func rname rargs) reductionA /= EQ && orderTerms (Func rname rargs) reductionRecB /= EQ ) 
            then (Axiom (reductionA,reductionRecB)):createRest
            else createRest
      where 
      (Func rname rargs) = renameVars (Func name args)
      reductionA = reduceTerm (ReductionRule (ruleA,resultA)) (Func rname rargs)
      reductionB = reduceTerm (ReductionRule (ruleB,resultB)) (Func rname rargs)
      reductionRecB = Func rname (mapOnlyFirst (reduceTerm (ReductionRule (ruleB,resultB))) rargs)
      mapOnlyFirst :: (Term -> Term) -> [Term] -> [Term]
      mapOnlyFirst f [] = []
      mapOnlyFirst f (a:args) =
        if orderTerms a b == EQ
          then a:(mapOnlyFirst f args)
          else b:args
        where b = f a
      createRest = createCritical (ReductionRule (ruleA,resultA)) (ReductionRule (ruleB,resultB)) rest

--better
createCriticalTerm :: Term -> Term -> [Term]
createCriticalTerm (Func nameA argsA) (Func nameB argsB) = 
    create (Func nameA argsA) (Func nameB argsB) (Func nameA argsA)
    where
    create :: Term -> Term -> Term ->[Term]
    create (Func nameA argsA) (Func nameB argsB) result = 
      if orderTerms (Func nameA argsA) (Func nameB argsB) == EQ
        then 
          superposeArgs argsA (Func nameB argsB) result
        else
          if checkSuperposition (Func nameA argsA) (Func nameB argsB) 
            then
              (superpose (Func nameA argsA) (Func nameB argsB) result):(superposeArgs argsA (Func nameB argsB) result)
            else
              superposeArgs argsA (Func nameB argsB) result


--write different
superpose :: Term -> Term -> Term -> Term
superpose termA termB termResult =
    bindingAtoB (fixedBindingBtoA (fixedBindingAtoB termResult))
    where 
    bindingAtoB :: Term -> Term
    bindingAtoB term = foldl (changeBinding) term (listBindedVars (ReductionRule (termA,termA)) termB) 
    bindingBtoA :: Term -> Term
    bindingBtoA term = foldl (changeBinding) term (listBindedVars (ReductionRule (termB,termB)) termA) 
    fixedBindingAtoB :: Term -> Term
    fixedBindingAtoB term = foldl (changeBinding) term (fix $ listBindedVars (ReductionRule (termA,termA)) termB) 
    fixedBindingBtoA :: Term -> Term
    fixedBindingBtoA term = foldl (changeBinding) term (fix $ listBindedVars (ReductionRule (termB,termB)) termA) 


fix :: [(Term,Term)] -> [(Term,Term)]
fix ((Var a,Var b):rest) = fix rest
fix ((Var v,Func name args):rest) = (Var v,Func name args):(fix rest)
fix [] = []

superposeArgs :: [Term] -> Term -> Term -> [Term]
superposeArgs ((Func nameA argsA):terms) termB termResult = 
    if checkSuperposition (Func nameA argsA) termB
      then 
        (superpose (Func nameA argsA) termB termResult):(superposeArgs terms termB termResult)
      else
        superposeArgs (terms++argsA) termB termResult
superposeArgs ((Var a):terms) termB termResult = 
    superposeArgs terms termB termResult
superposeArgs [] termB termResult = []

--end better

fixBindedVars :: [(Term,Term)] -> [(Term,Term)]
fixBindedVars bindings = 
   fix bindings bindings []
   where --change fix to work 
   fix :: [(Term,Term)] -> [(Term,Term)] -> [(Term,Term)] -> [(Term,Term)]
   fix [] input result = result
   fix ((Var v,Func name args):rest) input result = 
     fix rest input (result++[(Var v,Func name args)])
   fix ((Var v,Var r):rest) input result = 
     if isBindedToFunc (Var v,Var r) input
       then fix rest input result
       else fix rest input (result++[(Var v,Var r)])
     where
     isBindedToFunc :: (Term,Term) -> [(Term,Term)] -> Bool
     isBindedToFunc (Var v,Var r) [] = False 
     isBindedToFunc (Var v,Var r) ((Var b,Var a):rest) =
       isBindedToFunc (Var v,Var r) rest
     isBindedToFunc (Var v,Var r) ((Var b,Func name args):rest) =
       if v == b
         then True
         else isBindedToFunc (Var v,Var r) rest


reduceTerm :: ReductionRule -> Term -> Term
reduceTerm (ReductionRule (Func ruleName ruleArgs,result)) (Func name args) =
    if checkRuleInTerm (ReductionRule (Func ruleName ruleArgs,result)) (Func name args) 
      then swapTerm (ReductionRule (Func ruleName ruleArgs,result)) (Func name args)
      else Func name (mapOnlyFirst (reduceTerm (ReductionRule (Func ruleName ruleArgs, result))) args)
    where
    mapOnlyFirst :: (Term -> Term) -> [Term] -> [Term]
    mapOnlyFirst f [] = []
    mapOnlyFirst f (a:args) =
      if orderTerms a b == EQ --a == b
        then a:(mapOnlyFirst f args)
        else b:args
      where b = f a
    swapTerm :: ReductionRule -> Term -> Term
    swapTerm (ReductionRule (rule,result)) term = 
      foldl (changeBinding) result (listBindedVars (ReductionRule (rule,result)) term)
reduceTerm (ReductionRule (Func ruleName ruleArgs,result)) (Var v) = Var v

changeBinding :: Term -> (Term,Term) -> Term
changeBinding (Var t) (Var old, binded) = if (Var old) == (Var t) then binded else Var t
changeBinding (Func t args) (Var old, binded) = Func t (map (\x -> changeBinding x (Var old,binded)) args)


listBindedVars :: ReductionRule -> Term -> [(Term, Term)]
listBindedVars (ReductionRule (rule,result)) term = 
    bindedVars (ReductionRule (rule,result)) term (findVarsInTerm rule) [] 
    where
    bindedVars :: ReductionRule -> Term -> [Term] -> [(Term, Term)] -> [(Term,Term)]
    bindedVars _ _ [] binded = binded
    bindedVars (ReductionRule (rule, result)) term ((Var v):vars) binded =
      bindedVars (ReductionRule (rule, result)) term vars (binded ++ (getBinding (Var v) (rule,term)))
      where 
      getBinding :: Term -> (Term,Term) -> [(Term,Term)]
      getBinding (Var v) (Var a,term) = 
        if v == a 
          then [(Var v,term)]
          else [] 
      getBinding (Var v) (Func name args,Func termName termArgs) =
        concatMap (\(l,r) -> getBinding (Var v) (l,r)) list 
        where list = zip args termArgs 
      getBinding (Var v) (Func name args,Var a) =
        [(Var v,Var a)]

checkRuleInTerm :: ReductionRule -> Term -> Bool
checkRuleInTerm (ReductionRule (Func ruleFuncName ruleFuncArgs,result)) (Func name args) =
    if checkStructure (Func ruleFuncName ruleFuncArgs) (Func name args) 
      then checkBindedVars (listBindedVars (ReductionRule (Func ruleFuncName ruleFuncArgs,result)) (Func name args) )
      else False
    where 
    checkStructure :: Term -> Term -> Bool
    checkStructure (Var rv) _ = True
    checkStructure (Func rName rArgs) (Var v) = False
    checkStructure (Func rName rArgs) (Func name args) =
      if rName == name && length rArgs == length args
        then all (uncurry checkStructure) (zip rArgs args)
        else False
    checkBindedVars :: [(Term,Term)] -> Bool
    checkBindedVars [] = True
    checkBindedVars ((Var v,term):rest) =
      if checkBindedVar (Var v,term) rest
        then checkBindedVars rest
        else False
      where
      checkBindedVar :: (Term,Term) -> [(Term,Term)] -> Bool
      checkBindedVar (Var v,bindedTerm) [] = True
      checkBindedVar (Var v,bindedTerm) ((Var h,hTerm):rest) =
        if v == h 
          then bindedTerm == hTerm && (checkBindedVar (Var v,bindedTerm) rest)
          else checkBindedVar (Var v,bindedTerm) rest
    

isReducable :: ReductionRules -> Term -> Bool
isReducable [] t = False
isReducable (rule:rules) t =
    if isR rule t 
      then True
      else isReducable rules t
    where
    isR :: ReductionRule -> Term -> Bool
    isR (ReductionRule (Func rFuncName rFuncArgs, result)) (Var v) = False
    isR (ReductionRule (Func rFuncName rFuncArgs, result)) (Func name args) =
        if rFuncName == name && length rFuncArgs == length args
          then checkRuleInTerm (ReductionRule (Func rFuncName rFuncArgs, result)) (Func name args) 
          else any (isR (ReductionRule (Func rFuncName rFuncArgs, result))) args 


