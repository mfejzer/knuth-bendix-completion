{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings,CPP, DeriveDataTypeable, FlexibleContexts, GeneralizedNewtypeDeriving, 
    MultiParamTypeClasses #-}

module KnuthBendixCompletion.Datatypes where
import Data.Data (Data, Typeable)
import Data.Tree

data Term = Func String [Term] | Var String
    deriving (Eq, Ord, Read, Show, Data, Typeable)

data ReductionRule = ReductionRule (Term,Term)
    deriving (Eq, Ord, Read, Data, Typeable)

getRule (ReductionRule (rule,_)) = rule
getResult (ReductionRule (_,result)) = result

instance Show ReductionRule where
    show (ReductionRule (rule,result)) = show rule ++ " -> " ++ show result ++ "\n"

data Axiom = Axiom (Term,Term)
    deriving (Eq, Read, Data, Typeable)

instance Show Axiom where
    show (Axiom (l,r)) = "Axiom: " ++ show l ++ " <-> " ++ show r ++ "\n"

instance Ord Axiom where
    (<) axiomA axiomB = (maxLength axiomA) < (maxLength axiomB)
    (<=) axiomA axiomB = (maxLength axiomA) <= (maxLength axiomB)
    (>) axiomA axiomB = (maxLength axiomA) > (maxLength axiomB)
    (>=) axiomA axiomB = (maxLength axiomA) >= (maxLength axiomB)

maxLength :: Axiom -> Int
maxLength axiom = max ((getLength.lhs) axiom) ((getLength.rhs) axiom)

getLength :: Term -> Int	
getLength = length.findVarsInTerm 

type ReductionRules = [ReductionRule]
type Axioms = [Axiom]

groupAxioms = 
    [Axiom (Func "+" [Func "0" [],Var "x"],Var "x"),
            Axiom (Func "+" [Func "-" [Var "x"],Var "x"],Func "0" []),
            Axiom (Func "+" [Func "+" [Var "x",Var "y"],Var "z"],Func "+" [Var "x",Func "+" [Var "y",Var "z"]])]

lhs :: Axiom -> Term
lhs (Axiom (l,_)) = l

rhs :: Axiom -> Term
rhs (Axiom (_,r)) = r

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


