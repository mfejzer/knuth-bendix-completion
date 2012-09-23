{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, GeneralizedNewtypeDeriving, 
    MultiParamTypeClasses, TemplateHaskell, TypeFamilies, RecordWildCards #-}
module Persistance where
import Control.Applicative  ((<$>))
import Control.Exception    (bracket)
import Control.Monad        (msum)
import Control.Monad.Reader (ask)
import Control.Monad.State  (get, put)
import Data.Data (Data, Typeable)
import Data.Acid (AcidState, Query, Update, makeAcidic, openLocalState)
import Data.Acid.Advanced (query', update')
import Data.Acid.Local (createCheckpointAndClose)
import Data.SafeCopy (base, deriveSafeCopy)
import KnuthBendixCompletion.Datatypes
import KnuthBendixCompletion.Algorithm (kb)

deriveSafeCopy 0 'base ''Term
deriveSafeCopy 0 'base ''ReductionRule
deriveSafeCopy 0 'base ''Axiom

data ArgsState = ArgsState { args ::(Axioms,ReductionRules), nonOrientable::Maybe Axiom}
	deriving (Eq, Ord, Read, Show, Data, Typeable)
deriveSafeCopy 0 'base ''ArgsState

initialArgsState :: ArgsState
initialArgsState = ArgsState (groupAxioms,[]) Nothing 

updateArgs :: (Axioms, ReductionRules) -> Update ArgsState (Axioms, ReductionRules)
updateArgs newArgs =
    do a@ArgsState{..} <- get
       put $ a {args=newArgs,nonOrientable=Nothing}
       return args

peekArgs :: Query ArgsState (Axioms,ReductionRules)
peekArgs = args <$> ask

updateArgsByKBC :: Update ArgsState (Axioms, ReductionRules)
updateArgsByKBC = 
    do a@ArgsState{..} <- get
       let oldArgs = args
       if nonOrientable == Nothing
         then
           case (kb args) of
             (Left axiom) -> do 
               put $ a {args=oldArgs,nonOrientable = Just axiom}
               return args
             (Right newArgs) -> do 
               put $ a {args=newArgs,nonOrientable = Nothing} 
               return newArgs
         else
           return args

updateArgsToGroupAxioms :: Update ArgsState (Axioms, ReductionRules)
updateArgsToGroupAxioms = 
    do a@ArgsState{..} <- get
       let newArgs = (groupAxioms,[])
       put $ a {args=newArgs,nonOrientable=Nothing}
       return newArgs

$(makeAcidic ''ArgsState ['updateArgs,'updateArgsByKBC,'updateArgsToGroupAxioms,'peekArgs])
