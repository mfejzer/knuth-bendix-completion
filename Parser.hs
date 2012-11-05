module Parser where
import KnuthBendixCompletion.Datatypes
import Text.ParserCombinators.Parsec

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
    tb (')':xs) n     = ')':tb xs (n-1) 
    tb (x:xs)   n     = x:tb xs n


betterWords :: [Char] -> [[Char]]
betterWords text = bw text [] 0 where 
    bw :: [Char] -> [Char] -> Int -> [[Char]]
    bw (' ':xs) tmpWord 0     = tmpWord:bw xs [] 0
    bw ('(':xs) tmpWord 0     = bw xs tmpWord 1
    bw ('(':xs) tmpWord n     = bw xs (tmpWord ++ ['(']) (n+1)
    bw (x:xs)   tmpWord 0     = bw xs (tmpWord ++ [x]) 0
    bw (')':xs) tmpWord 1     = bw xs tmpWord 0
    bw (')':xs) tmpWord n = bw xs (tmpWord ++ [')']) (n-1)
    bw (x:xs)   tmpWord n     = bw xs (tmpWord ++ [x]) n
    bw []       tmpWord n     = [tmpWord]

parseAxiom :: String -> Either ParseError Axiom
parseAxiom input = parse axiomParser "(unknown)" input

parseReductionRule :: String -> Either ParseError ReductionRule
parseReductionRule input = parse reductionRuleParser "(unknown)" input

parseTerm :: String -> Either ParseError Term
parseTerm input = parse termParser "(unknown)" input

convertError :: Either ParseError a -> Either String a
convertError (Left e) = (Left $ show e)
convertError (Right a) = (Right a)

axiomParser :: GenParser Char st Axiom
axiomParser = do
	lhs <- termParser
	string "<->"
	rhs <- termParser
	return $ Axiom (lhs,rhs)

reductionRuleParser :: GenParser Char st ReductionRule
reductionRuleParser = do
	parsedRule <- termParser
	string "->"
	parsedResult <- termParser
	return $ ReductionRule {rule=parsedRule,result=parsedResult}

termParser :: GenParser Char st Term
termParser = do
	result <- try (funcParser) <|> varParser
	return $ result


varParser :: GenParser Char st Term
varParser = do
	name <- nameParser
	return $ Var name

funcParser :: GenParser Char st Term
funcParser = do
	name <- nameParser
	char '('
	args <- argsParser
	char ')'
	return $ Func name args

argsParser :: GenParser Char st [Term]
argsParser = do
	args <- sepBy termParser (char ',')
	return $ args	

nameParser :: GenParser Char st String
nameParser = do
	result <- many1 (noneOf ",()\n")
	return $ result
