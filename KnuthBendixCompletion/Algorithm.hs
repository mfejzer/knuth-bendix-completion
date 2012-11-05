module KnuthBendixCompletion.Algorithm where
import KnuthBendixCompletion.Datatypes
import Data.List (sort)

kbc :: ([Axiom],[ReductionRule]) -> Either Axiom ([Axiom],[ReductionRule])
kbc args =
    case result of
      (Left error) -> Left error
      (Right newArgs) -> 
        if newArgs == args 
          then Right newArgs
          else kbc newArgs
    where result = kb args

kb :: ([Axiom],[ReductionRule]) -> Either Axiom ([Axiom],[ReductionRule])
kb ([],rules) = Right ([],rules)
kb (axioms,rules) = 
      if compareTerms axiomLhs axiomRhs == EQ && (not $ checkLexEq axiomLhs axiomRhs)
	then Left normalisedAxiom
	else
          if (compareTerms axiomLhs axiomRhs /= EQ) && (not $ elem rule rules)
            then Right (superposeRules rule newRules restAxioms, newRules)
            else Right (restAxioms,rules)
      where (axiom,restAxioms) = takeAxiom axioms
            normalisedAxiom = normaliseAxiom axiom rules
            axiomLhs = lhs normalisedAxiom
            axiomRhs = rhs normalisedAxiom
            rule = renameVarsInReductionRuleWithPrefix "" (orderAxiom normalisedAxiom)
            newRules = makeNewRules rule rules


--simple, todo: complicated
takeAxiom :: [Axiom] -> (Axiom,[Axiom])
takeAxiom axioms = (head sortedAxioms, tail sortedAxioms)
    where
    sortedAxioms = axioms --List.sort axioms


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
reduceRule reductingRule (ReductionRule {rule=ruleTerm,result=resultTerm}) =
    if compareTerms reducedRule reducedResult /= EQ
      then
      if compareTerms reducedRule reducedResult /= LT
        then Just (ReductionRule {rule=reducedRule,result=reducedResult})
        else Just (ReductionRule {rule=reducedResult,result=reducedRule})
      else Nothing
    where reducedRule = reduceTerm reductingRule ruleTerm
          reducedResult = reduceTerm reductingRule resultTerm

normaliseAxiom :: Axiom -> [ReductionRule] -> Axiom
normaliseAxiom (Axiom (termA,termB)) rules = 
    (Axiom (reduceToNormalised rules termA,reduceToNormalised rules termB))

reduceToNormalised :: [ReductionRule] -> Term -> Term
reduceToNormalised rules term = 
    if compareTerms result term == EQ
      then term
      else reduceToNormalised rules result
    where result = reduce rules term

reduce :: [ReductionRule] -> Term -> Term
reduce [] term = term
reduce (rule:rest) term =
    if compareTerms result term == EQ
      then reduce rest term
      else result
    where result = reduceTerm renamedRule term
          renamedRule = renameVarsInReductionRuleWithPrefix "r" rule 

orderAxiom :: Axiom -> ReductionRule 
orderAxiom a = 
    if compareTerms (lhs a) (rhs a) == GT 
      then (ReductionRule {rule=lhs a,result=rhs a}) 
      else (ReductionRule {rule = rhs a,result =lhs a})

compareTerms :: Term -> Term -> Ordering
compareTerms termA termB =
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


checkLexEq :: Term -> Term -> Bool
checkLexEq (Var x) (Var y) = x==y
checkLexEq (Func f argsF) (Func g argsG) = foldr (&&) (f==g) (map (\(x,y) -> checkLexEq x y) (zip argsF argsG))


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
    find ruleA ruleB axioms =
        if checkCriticalPair (rule renamedRuleA) (rule renamedRuleB)
          then addCriticalPair renamedRuleA renamedRuleB axioms
          else axioms
      where renamedRuleA = renameVarsInReductionRuleWithPrefix "l" ruleA
            renamedRuleB = renameVarsInReductionRuleWithPrefix "r" ruleB


checkCriticalPair :: Term -> Term -> Bool 
checkCriticalPair (Func nameA argsA) (Func nameB argsB) =
    if compareTerms (Func nameA argsA) (Func nameB argsB) == EQ
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
      then checkBindedVars $ fixBindedVars (listBindedVars (ReductionRule {rule=Func nameA argsA,result=Func nameA argsA}) (Func nameB argsB))
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
createCriticalPair (ReductionRule {rule=ruleA,result=resultA}) (ReductionRule {rule=ruleB,result=resultB}) =
    createCritical (ReductionRule {rule=ruleA,result=resultA}) (ReductionRule {rule=ruleB,result=resultB}) (createCriticalTerm ruleA ruleB)
    where
    createCritical :: ReductionRule -> ReductionRule -> [Term] -> [Axiom]
    createCritical _ _ [] = []
    createCritical (ReductionRule {rule=ruleA,result=resultA}) (ReductionRule {rule=ruleB,result=resultB}) ((Func name args):rest) = 
      if compareTerms ruleA ruleB /= EQ
        then
          if (compareTerms (Func rname rargs) reductionA /= EQ && compareTerms (Func rname rargs) reductionB /= EQ ) 
            then (Axiom (reductionA,reductionB)):createRest
            else createRest
        else
          if (compareTerms (Func rname rargs) reductionA /= EQ && compareTerms (Func rname rargs) reductionRecB /= EQ ) 
            then (Axiom (reductionA,reductionRecB)):createRest
            else createRest
      where 
      (Func rname rargs) = renameVars (Func name args)
      reductionA = reduceTerm (ReductionRule {rule=ruleA,result=resultA}) (Func rname rargs)
      reductionB = reduceTerm (ReductionRule {rule=ruleB,result=resultB}) (Func rname rargs)
      reductionRecB = Func rname (mapOnlyFirst (reduceTerm (ReductionRule {rule=ruleB,result=resultB})) rargs)
      mapOnlyFirst :: (Term -> Term) -> [Term] -> [Term]
      mapOnlyFirst f [] = []
      mapOnlyFirst f (a:args) =
        if compareTerms a b == EQ
          then a:(mapOnlyFirst f args)
          else b:args
        where b = f a
      createRest = createCritical (ReductionRule {rule=ruleA,result=resultA}) (ReductionRule {rule=ruleB,result=resultB}) rest

--better
createCriticalTerm :: Term -> Term -> [Term]
createCriticalTerm (Func nameA argsA) (Func nameB argsB) = 
    create (Func nameA argsA) (Func nameB argsB) (Func nameA argsA)
    where
    create :: Term -> Term -> Term ->[Term]
    create (Func nameA argsA) (Func nameB argsB) result = 
      if compareTerms (Func nameA argsA) (Func nameB argsB) == EQ
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
    bindingAtoB term = foldl (changeBinding) term (listBindedVars (ReductionRule {rule=termA,result=termA}) termB) 
    bindingBtoA :: Term -> Term
    bindingBtoA term = foldl (changeBinding) term (listBindedVars (ReductionRule {rule=termB,result=termB}) termA) 
    fixedBindingAtoB :: Term -> Term
    fixedBindingAtoB term = foldl (changeBinding) term (fix $ listBindedVars (ReductionRule {rule=termA,result=termA}) termB) 
    fixedBindingBtoA :: Term -> Term
    fixedBindingBtoA term = foldl (changeBinding) term (fix $ listBindedVars (ReductionRule {rule=termB,result=termB}) termA) 


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
reduceTerm rr (Func name args) =
    if checkRuleInTerm (rr) (Func name args) 
      then swapTerm (rr) (Func name args)
      else Func name (mapOnlyFirst (reduceTerm rr) args)
    where
    mapOnlyFirst :: (Term -> Term) -> [Term] -> [Term]
    mapOnlyFirst f [] = []
    mapOnlyFirst f (a:args) =
      if compareTerms a b == EQ --a == b
        then a:(mapOnlyFirst f args)
        else b:args
      where b = f a
    swapTerm :: ReductionRule -> Term -> Term
    swapTerm rr term = 
      foldl (changeBinding) (result rr) (listBindedVars rr term)
reduceTerm (rr) (Var v) = Var v

changeBinding :: Term -> (Term,Term) -> Term
changeBinding (Var t) (Var old, binded) = if (Var old) == (Var t) then binded else Var t
changeBinding (Func t args) (Var old, binded) = Func t (map (\x -> changeBinding x (Var old,binded)) args)


listBindedVars :: ReductionRule -> Term -> [(Term, Term)]
listBindedVars rr term = 
    bindedVars rr term (findVarsInTerm (rule rr)) [] 
    where
    bindedVars :: ReductionRule -> Term -> [Term] -> [(Term, Term)] -> [(Term,Term)]
    bindedVars _ _ [] binded = binded
    bindedVars rr term ((Var v):vars) binded =
      bindedVars rr term vars (binded ++ (getBinding (Var v) (rule rr,term)))
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
checkRuleInTerm (ReductionRule {rule=Func ruleFuncName ruleFuncArgs,result=res}) (Func name args) =
    if checkStructure (Func ruleFuncName ruleFuncArgs) (Func name args) 
      then checkBindedVars (listBindedVars (ReductionRule {rule=Func ruleFuncName ruleFuncArgs,result=res}) (Func name args) )
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
    


