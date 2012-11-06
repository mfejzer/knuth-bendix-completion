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
deriveSafeCopy 0 'base ''AlgorithmStatus

initialAlgorithmStatus :: AlgorithmStatus
initialAlgorithmStatus = CanProceed {axioms=groupAxioms,rules=[]}

peekAlgorithmStatus :: Query AlgorithmStatus AlgorithmStatus
peekAlgorithmStatus = ask

updateAlgorithmStatusByKBC :: Update AlgorithmStatus AlgorithmStatus 
updateAlgorithmStatusByKBC = 
    do state <- get
       case state of
         (CanProceed _ _) -> do 
           put (kb state)
           return (kb state)
         (Finished  _) -> return state
         (FailedOn _ _ _) -> return state

$(makeAcidic ''AlgorithmStatus ['updateAlgorithmStatusByKBC,'peekAlgorithmStatus])
