module Commands where

data Command = LogIn | LogOut | RunAlgorithm | AddAxiom | AddRule | RemoveAxiom | RemoveAllAxioms | RemoveRule | RemoveAllRules | Reset
    deriving (Eq, Ord, Read, Show)

