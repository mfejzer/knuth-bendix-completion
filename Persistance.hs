{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, GeneralizedNewtypeDeriving, 
    MultiParamTypeClasses, TemplateHaskell, TypeFamilies, RecordWildCards,TypeSynonymInstances,FlexibleInstances #-}
module Persistance where
import Auth.Datatypes
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

type AppStatus = AppStatusTemplate AlgorithmStatus

deriveSafeCopy 0 'base ''Term
deriveSafeCopy 0 'base ''ReductionRule
deriveSafeCopy 0 'base ''Axiom
deriveSafeCopy 0 'base ''AlgorithmStatus
deriveSafeCopy 0 'base ''SessionHash
deriveSafeCopy 0 'base ''User
deriveSafeCopy 0 'base ''AppStatusTemplate
deriveSafeCopy 0 'base ''LogInResult
deriveSafeCopy 0 'base ''CheckHashResult
deriveSafeCopy 0 'base ''LogOutResult
{-deriveSafeCopy 0 'base ''AppStatus-}

initialAlgorithmStatus :: AlgorithmStatus
initialAlgorithmStatus = CanProceed {axioms=groupAxioms,rules=[]}

initialAppStatus:: AppStatus
initialAppStatus = AppStatusTemplate ([User "admin" "pass" initialAlgorithmStatus Nothing])

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

logInUser :: Login -> Password -> SessionHash -> Update AppStatus LogInResult
logInUser l p sh =
    do state <- get
       let (result,newState) = logIn state l p sh
       put newState
       return result
       
checkHashUser :: SessionHash -> Query AppStatus CheckHashResult
checkHashUser sh = (\state -> checkHash state sh) <$> ask

logOutUser :: SessionHash -> Update AppStatus LogOutResult
logOutUser sh =
    do state <- get
       let (result,newState) = logOut state sh
       put newState
       return result

peekAppStatus :: Query AppStatus AppStatus
peekAppStatus = ask


$(makeAcidic ''AppStatus ['logInUser,'logOutUser,'peekAppStatus])
