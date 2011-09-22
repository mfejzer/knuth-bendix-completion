
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
kbCompletion (Axioms axioms) = kb (Axioms axioms) (ReductionRules []) where
    kb :: Axioms -> ReductionRules -> ReductionRules
    kb (Axioms [])     (ReductionRules rules) = (ReductionRules rules)
    kb (Axioms axioms) (ReductionRules rules) = 
      if (lhs normalisedAxiom) /= (rhs normalisedAxiom)
        then kb (superpose rule (ReductionRules (rules++[rule])) restAxioms) (ReductionRules (rules++[rule]))
        else kb restAxioms (ReductionRules rules)
      where (axiom,restAxioms) = takeAxiom (Axioms axioms); 
            normalisedAxiom = normaliseAxiom axiom (ReductionRules rules); 
            rule = orderAxiom normalisedAxiom

--todo
normaliseAxiom :: Axiom -> ReductionRules -> Axiom
normaliseAxiom a _ = a

orderAxiom :: Axiom -> ReductionRule 
orderAxiom a = if (lhs a) > (rhs a) then (ReductionRule (lhs a,rhs a)) else (ReductionRule (rhs a,lhs a))

--ready
superpose :: ReductionRule -> ReductionRules -> Axioms -> Axioms
superpose (ReductionRule rule) (ReductionRules []) (Axioms axioms) = (Axioms axioms)
superpose (ReductionRule rule) (ReductionRules (r:rules)) (Axioms axioms) =
    superpose (ReductionRule rule) (ReductionRules rules) newAxioms where
      newAxioms = findCriticalPair (ReductionRule rule) r (Axioms axioms)

--todo
findCriticalPair :: ReductionRule -> ReductionRule -> Axioms -> Axioms
findCriticalPair (ReductionRule (termA,_)) (ReductionRule (termB,_)) axioms = axioms

--remove from here    
--tmp ready, try to change list in reduce to single parameter
reduceTerm2 :: ReductionRule -> Term -> Term
reduceTerm2 (ReductionRule (Func ruleName ruleArgs,result)) (Func name args) =
    reduce (ReductionRule (Func ruleName ruleArgs,result)) [(Func name args)]
    where
    reduce :: ReductionRule -> [Term] -> Term
    reduce (ReductionRule (Func ruleName ruleArgs,result)) ((Func name args):terms) =
      if ruleName == name && length args == length ruleArgs 
        then swapTerm (ReductionRule (Func ruleName ruleArgs,result)) (Func name args) --result
        else Func name (map (\x -> reduce (ReductionRule (Func ruleName ruleArgs, result)) (terms++[x])) args)
--      where newTerms = filter isFunc args
    reduce (ReductionRule (Func ruleName ruleArgs,result)) ((Var v):terms) = Var v

-- not ready tmp without list
reduceTerm :: ReductionRule -> Term -> Term
reduceTerm (ReductionRule (Func ruleName ruleArgs,result)) (Func name args) =
    if checkRuleInTerm (ReductionRule (Func ruleName ruleArgs,result)) (Func name args) 
      then swapTerm (ReductionRule (Func ruleName ruleArgs,result)) (Func name args) 
      else Func name (map (reduceTerm (ReductionRule (Func ruleName ruleArgs, result))) args)
reduceTerm (ReductionRule (Func ruleName ruleArgs,result)) (Var v) = Var v

-- tmp 3 version, works but horrible written, current good
reduceTerm3 :: ReductionRule -> Term -> Term
reduceTerm3 (ReductionRule (Func ruleName ruleArgs,result)) (Func name args) =
    if checkRuleInTerm (ReductionRule (Func ruleName ruleArgs,result)) (Func name args) 
      then swapTerm (ReductionRule (Func ruleName ruleArgs,result)) (Func name args) 
      else Func name (onlyFirst False (map (\x -> (x ,reduceTerm (ReductionRule (Func ruleName ruleArgs, result)) x)) args))
    where
    onlyFirst :: Bool -> [(Term, Term)] -> [Term]
    onlyFirst False ((a,b):rest) = 
      if a == b
        then a:onlyFirst False rest
        else b:onlyFirst True rest
    onlyFirst True ((a,b):rest) = a:onlyFirst True rest
    onlyFirst True [] = []
reduceTerm3 (ReductionRule (Func ruleName ruleArgs,result)) (Var v) = Var v

--ready
swapTerm :: ReductionRule -> Term -> Term
swapTerm (ReductionRule (rule,result)) term = 
   foldl (changeBinding) result (listBindedVars (ReductionRule (rule,result)) term)

--ready
changeBinding :: Term -> (Term,Term) -> Term
changeBinding (Var t) (Var old, binded) = if (Var old) == (Var t) then binded else Var t
changeBinding (Func t args) (Var old, binded) = Func t (map (\x -> changeBinding x (Var old,binded)) args)


--new try works in simple cases 
listBindedVars :: ReductionRule -> Term -> [(Term, Term)]
listBindedVars (ReductionRule (rule,result)) term = 
    bindedVars (ReductionRule (rule,result)) term (findVarsInTerm result) [] 
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

--ready
checkRuleInTerm :: ReductionRule -> Term -> Bool
checkRuleInTerm (ReductionRule (Func ruleFuncName ruleFuncArgs,result)) (Func name args) =
    if ruleFuncName == name && length ruleFuncArgs == length args
      then check (Func ruleFuncName ruleFuncArgs) (Func name args) 
      else False
    where 
    check :: Term -> Term -> Bool
    check (Var rv) _ = True
    check (Func rName rArgs) (Func name args) =
      if rName == name && length rArgs == length args
        then all (uncurry check) (zip rArgs args)
        else False

--ready 
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



isFunc :: Term -> Bool
isFunc (Func a b) = True 
isFunc (Var v) = False

--translateReduction :: String -> String -> ReductionRule
--translateReduction a b = ReductionRule (max termA termB,min termA termB) where termA = translate a; termB = translate b

--checkReduction :: ReductionRule -> Bool
--checkReduction (ReductionRule (term, (Var v))) = checkVarInTerm (Var v) term
--checkReduction (ReductionRule (term, (Func name args))) = and (map (\x -> checkReduction (ReductionRule (term, x))) args)


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

