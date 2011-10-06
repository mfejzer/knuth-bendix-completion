module KnuthBendixCompletion where

data Term = Func String [Term] | Var String
    deriving (Eq, Ord, Read, Show)

data ReductionRule = ReductionRule (Term,Term)
    deriving (Eq, Ord, Read, Show)

data Axiom = Axiom (Term,Term)
    deriving (Eq, Ord, Read, Show)

data ReductionRules = ReductionRules [ReductionRule]
    deriving (Eq, Ord, Read, Show)

data Axioms = Axioms [Axiom]
    deriving (Eq, Ord, Read, Show)

lhs :: Axiom -> Term
lhs (Axiom (l,_)) = l

rhs :: Axiom -> Term
rhs (Axiom (_,r)) = r

--simple, todo: complicated
takeAxiom :: Axioms -> (Axiom,Axioms)
takeAxiom (Axioms (a:axioms)) = (a,Axioms axioms)

--ready
kbCompletion :: Axioms -> ReductionRules
kbCompletion (Axioms axioms) = kb (Axioms axioms) (ReductionRules []) --where

kb :: Axioms -> ReductionRules -> ReductionRules
kb (Axioms [])     (ReductionRules rules) = (ReductionRules rules)
kb (Axioms axioms) (ReductionRules rules) = 
      if orderTerms (lhs normalisedAxiom) (rhs normalisedAxiom) /= EQ && (not $ elem rule rules)
        then 
          kb (superposeRules rule (ReductionRules newRules) (Axioms axioms)) (ReductionRules newRules)
        else 
          kb restAxioms (ReductionRules rules)
      where (axiom,restAxioms) = takeAxiom (Axioms axioms); 
            normalisedAxiom = normaliseAxiom axiom (ReductionRules rules); 
            rule = renameVarsInReductionRuleWithPrefix "" (orderAxiom normalisedAxiom)
            newRules = rules++[rule]

normaliseAxiom :: Axiom -> ReductionRules -> Axiom
normaliseAxiom (Axiom (termA,termB)) rules = 
    (Axiom (reduceToNormalised rules termA,reduceToNormalised rules termB))

reduceToNormalised :: ReductionRules -> Term -> Term
reduceToNormalised (ReductionRules rules) term = 
    if orderTerms result term == EQ
      then term
      else reduceToNormalised (ReductionRules rules) result
    where result = reduce (ReductionRules rules) term

reduce :: ReductionRules -> Term -> Term
reduce (ReductionRules []) term = term
reduce (ReductionRules (rule:rest)) term =
    if orderTerms result term == EQ
      then reduce (ReductionRules rest) term
      else result
    where result = reduceTerm rule term

orderAxiom :: Axiom -> ReductionRule 
orderAxiom a = if orderTerms (lhs a) (rhs a) == GT then (ReductionRule (lhs a,rhs a)) else (ReductionRule (rhs a,lhs a))

orderTerms :: Term -> Term -> Ordering
orderTerms (Func name args) (Var v) = GT
orderTerms (Var v) (Func name args) = LT
orderTerms (Var a) (Var b) = EQ
orderTerms (Func nameA (a:argsA)) (Func nameB (b:argsB)) =
    if order == EQ
      then orderTerms (Func nameA argsA) (Func nameB argsB)
      else order
    where order = orderTerms a b
orderTerms (Func nameA []) (Func nameB []) = EQ
orderTerms (Func nameA (a:args)) (Func nameB []) = GT
orderTerms (Func nameA []) (Func nameB (b:args)) = LT


superposeRules :: ReductionRule -> ReductionRules -> Axioms -> Axioms
superposeRules (ReductionRule rule) (ReductionRules []) (Axioms axioms) = (Axioms axioms)
superposeRules (ReductionRule rule) (ReductionRules (r:rules)) (Axioms axioms) =
    superposeRules (ReductionRule rule) (ReductionRules rules) newAxioms where
      newAxioms = findCriticalPair (ReductionRule rule) r (Axioms axioms)


findCriticalPair :: ReductionRule -> ReductionRule -> Axioms -> Axioms
findCriticalPair ruleA ruleB axioms=
    find ruleB ruleA $ find ruleA ruleB axioms
    where
    find :: ReductionRule -> ReductionRule -> Axioms -> Axioms
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
          else any (\a -> checkSuperposition a (Func nameB argsB)) argsA
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
    checkStructure (Func aName (a:aArgs)) (Var bV) = True --propably!
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

addCriticalPair :: ReductionRule -> ReductionRule -> Axioms -> Axioms
addCriticalPair ruleA ruleB (Axioms axioms) = 
    add ruleA ruleB (Axioms axioms) (createCriticalPair ruleA ruleB)
    where
    add :: ReductionRule -> ReductionRule -> Axioms -> Maybe Axiom -> Axioms
    add ruleA ruleB (Axioms axioms) (Nothing) = (Axioms axioms) 
    add ruleA ruleB (Axioms axioms) (Just axiom) = 
      if not (elem axiom axioms)
        then (Axioms (axioms++[axiom]))
        else (Axioms axioms)

createCriticalPair :: ReductionRule -> ReductionRule -> Maybe Axiom
createCriticalPair (ReductionRule (ruleA,resultA)) (ReductionRule (ruleB,resultB)) =
    createCritical (ReductionRule (ruleA,resultA)) (ReductionRule (ruleB,resultB)) (createCriticalTerm ruleA ruleB)
    where
    createCritical :: ReductionRule -> ReductionRule -> Maybe Term -> Maybe Axiom
    createCritical _ _ Nothing = Nothing
    createCritical (ReductionRule (ruleA,resultA)) (ReductionRule (ruleB,resultB)) (Just (Func name args)) = 
      if orderTerms ruleA ruleB /= EQ
        then
          if (orderTerms (Func rname rargs) reductionA /= EQ && orderTerms (Func rname rargs) reductionB /= EQ ) 
            then Just (Axiom (reductionA,reductionB))
            else Nothing
        else
          if (orderTerms (Func rname rargs) reductionA /= EQ && orderTerms (Func rname rargs) reductionRecB /= EQ ) 
            then Just (Axiom (reductionA,reductionRecB)) 
            else Nothing
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

--better
createCriticalTerm :: Term -> Term -> Maybe Term
createCriticalTerm (Func nameA argsA) (Func nameB argsB) = 
    create (Func nameA argsA) (Func nameB argsB) (Func nameA argsA)
    where
    create :: Term -> Term -> Term -> Maybe Term
    create (Func nameA argsA) (Func nameB argsB) result = 
      if orderTerms (Func nameA argsA) (Func nameB argsB) == EQ
        then 
          superposeArgs argsA (Func nameB argsB) result
        else
          if checkSuperposition (Func nameA argsA) (Func nameB argsB) 
            then
              superpose (Func nameA argsA) (Func nameB argsB) result
            else
              superposeArgs argsA (Func nameB argsB) result

superpose :: Term -> Term -> Term -> Maybe Term
superpose termA termB termResult =
    Just $ bindingAtoB (fixedBindingBtoA (fixedBindingAtoB termResult))
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

superposeArgs :: [Term] -> Term -> Term -> Maybe Term 
superposeArgs ((Func nameA argsA):terms) termB termResult = 
    if checkSuperposition (Func nameA argsA) termB
      then 
        superpose (Func nameA argsA) termB termResult
      else
        superposeArgs (terms++argsA) termB termResult
superposeArgs ((Var a):terms) termB termResult = 
    superposeArgs terms termB termResult
superposeArgs [] termB termResult = Nothing

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
      if a == b
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
isReducable (ReductionRules []) t = False
isReducable (ReductionRules (rule:rules)) t =
    if isR rule t 
      then True
      else isReducable (ReductionRules rules) t
    where
    isR :: ReductionRule -> Term -> Bool
    isR (ReductionRule (Func rFuncName rFuncArgs, result)) (Var v) = False
    isR (ReductionRule (Func rFuncName rFuncArgs, result)) (Func name args) =
        if rFuncName == name && length rFuncArgs == length args
          then checkRuleInTerm (ReductionRule (Func rFuncName rFuncArgs, result)) (Func name args) 
          else any (isR (ReductionRule (Func rFuncName rFuncArgs, result))) args 


renameVars :: Term -> Term
renameVars = renameVarsWithPrefix ""

renameVarsWithPrefix :: String -> Term -> Term
renameVarsWithPrefix prefix term = rename prefix term (findVarsInTerm term) 0 where
    rename :: String -> Term -> [Term] -> Int -> Term
    rename prefix term [] n = term
    rename prefix term (v:vars) n = rename prefix (changeVarInTerm v (Var (prefix++('v':(show n)))) term) vars (n+1)

renameVarsInReductionRule :: ReductionRule -> ReductionRule
renameVarsInReductionRule (ReductionRule (rule,result)) = rename (ReductionRule (rule,result)) (findVarsInTerm rule) 0 where
    rename :: ReductionRule -> [Term] -> Int -> ReductionRule
    rename (ReductionRule (rule,result)) [] n = (ReductionRule (rule,result))
    rename (ReductionRule (rule,result)) (v:vars) n = 
      rename (ReductionRule (changeVarInTerm v (Var ('v':(show n))) rule,changeVarInTerm v (Var ('v':(show n))) result)) vars (n+1)

renameVarsInReductionRuleWithPrefix :: String -> ReductionRule -> ReductionRule
renameVarsInReductionRuleWithPrefix prefix (ReductionRule (rule,result)) = rename prefix (ReductionRule (rule,result)) (findVarsInTerm rule) 0 where
    rename :: String -> ReductionRule -> [Term] -> Int -> ReductionRule
    rename prefix (ReductionRule (rule,result)) [] n = (ReductionRule (rule,result))
    rename prefix (ReductionRule (rule,result)) (v:vars) n = 
      rename prefix (ReductionRule (changeVarInTerm v (Var (prefix++('v':(show n)))) rule,changeVarInTerm v (Var (prefix++('v':(show n)))) result)) vars (n+1)


isFunc :: Term -> Bool
isFunc (Func a b) = True 
isFunc (Var v) = False

checkVarInTerm :: Term -> Term -> Bool
checkVarInTerm (Var v) (Var t) = v == t
checkVarInTerm (Var v) (Func t args) = or (map (\x -> checkVarInTerm (Var v) x) args)

changeVarInTerm :: Term -> Term -> Term -> Term
changeVarInTerm (Var old) (Var new) (Var t) = if (Var old) == (Var t) then Var new else Var t
changeVarInTerm (Var old) (Var new) (Func t args) = Func t (map (\x -> changeVarInTerm (Var old) (Var new) x) args)

findVarsInTerm :: Term -> [Term]
findVarsInTerm t = removeDuplicateVars (findVars t []) where
    findVars :: Term -> [Term] -> [Term]
    findVars (Var v) vars = (Var v):vars
    findVars (Func f []) vars = vars
    findVars (Func f (a:args)) vars = findVars (Func f args) (findVars a vars)
    removeDuplicateVars :: [Term] -> [Term] 
    removeDuplicateVars vars = removeDuplicates vars [] where 
        removeDuplicates :: [Term] -> [Term] -> [Term]
        removeDuplicates [] result = result
        removeDuplicates (v:vars) result = if elem v result 
          then removeDuplicates vars result 
          else removeDuplicates vars (v:result)


normaliseTerm :: Term -> Term
normaliseTerm term = normalise term (findVarsInTerm term) 0 where
    normalise :: Term -> [Term] -> Int -> Term
    normalise term [] n = term
    normalise term (v:vars) n = normalise (changeVarInTerm v (Var ('v':(show n))) term) vars (n+1)


translate :: String -> Term
translate ('(':text) = (translate.takeBrackets) ('(':text)
translate text = 
    if (length.betterWords) text == 1
      then Var text
      else Func funcName (map translate funcArgs) where funcName:funcArgs = betterWords text


takeBrackets :: [Char] -> [Char]
takeBrackets text = tb text 0 where 
    tb :: [Char] -> Int -> [Char]
    tb []       _     = []
    tb ('(':xs) 0     = tb xs 1 
    tb ('(':xs) n     = '(':tb xs (n+1)
    tb (')':xs) 1     = tb xs 0
    tb (')':xs) (n+1) = ')':tb xs n
    tb (x:xs)   n     = x:tb xs n


betterWords :: [Char] -> [[Char]]
betterWords text = bw text [] 0 where 
    bw :: [Char] -> [Char] -> Int -> [[Char]]
    bw (' ':xs) tmpWord 0     = tmpWord:bw xs [] 0
    bw ('(':xs) tmpWord 0     = bw xs tmpWord 1
    bw ('(':xs) tmpWord n     = bw xs (tmpWord ++ ['(']) (n+1)
    bw (x:xs)   tmpWord 0     = bw xs (tmpWord ++ [x]) 0
    bw (')':xs) tmpWord 1     = bw xs tmpWord 0
    bw (')':xs) tmpWord (n+1) = bw xs (tmpWord ++ [')']) n
    bw (x:xs)   tmpWord n     = bw xs (tmpWord ++ [x]) n
    bw []       tmpWord n     = [tmpWord]

