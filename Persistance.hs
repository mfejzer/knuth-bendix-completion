{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, GeneralizedNewtypeDeriving, 
    MultiParamTypeClasses, TemplateHaskell, TypeFamilies, RecordWildCards,TypeSynonymInstances,FlexibleInstances #-}
module Persistance where
import Auth
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


$(makeAcidic ''AlgorithmStatus [])

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

updateAlgorithmStatus :: SessionHash -> (AlgorithmStatus -> AlgorithmStatus) -> Update AppStatus (Maybe AlgorithmStatus)
updateAlgorithmStatus sh f = 
    do state <- get
       let (result,newState) = updateUserContent state f sh
       put newState
       return result

updateAlgorithmStatusByKBC :: SessionHash -> Update AppStatus (Maybe AlgorithmStatus)
updateAlgorithmStatusByKBC sh = updateAlgorithmStatus sh rkbc
    where
    rkbc :: AlgorithmStatus -> AlgorithmStatus
    rkbc status =
       case status of
         (CanProceed _ _) -> kb status
         (Finished  _) -> status
         (FailedOn _ _ _) -> status

updateAlgorithmStatusByAddingAxiom :: SessionHash -> Axiom -> Update AppStatus (Maybe AlgorithmStatus)
updateAlgorithmStatusByAddingAxiom sh axiom = updateAlgorithmStatus sh (addAxiom axiom)
    where
    addAxiom :: Axiom -> AlgorithmStatus -> AlgorithmStatus
    addAxiom axiom status =
      case status of
         (CanProceed a r) -> (CanProceed (a++[axiom]) r)
         (Finished  _) -> status
         (FailedOn _ _ _) -> status

updateAlgorithmStatusByAddingRule :: SessionHash -> ReductionRule -> Update AppStatus (Maybe AlgorithmStatus)
updateAlgorithmStatusByAddingRule sh rule = updateAlgorithmStatus sh (addRule rule)
    where
    addRule :: ReductionRule -> AlgorithmStatus -> AlgorithmStatus
    addRule rule status =
      case status of
         (CanProceed a r) -> (CanProceed a (r++[rule]))
         (Finished  _) -> status
         (FailedOn _ _ _) -> status

updateAlgorithmStatusByRemovingAxioms :: SessionHash -> Update AppStatus (Maybe AlgorithmStatus)
updateAlgorithmStatusByRemovingAxioms sh = updateAlgorithmStatus sh removeAxioms
    where
    removeAxioms:: AlgorithmStatus -> AlgorithmStatus
    removeAxioms status =
      case status of
         (CanProceed a r) -> (CanProceed [] r)
         (Finished  _) -> status
         (FailedOn _ _ _) -> status

updateAlgorithmStatusByRemovingRules :: SessionHash -> Update AppStatus (Maybe AlgorithmStatus)
updateAlgorithmStatusByRemovingRules sh = updateAlgorithmStatus sh removeRules
    where
    removeRules :: AlgorithmStatus -> AlgorithmStatus
    removeRules status =
      case status of
         (CanProceed a r) -> (CanProceed a [])
         (Finished  _) -> status
         (FailedOn _ _ _) -> status

updateAlgorithmStatusByDefaultReset :: SessionHash -> Update AppStatus (Maybe AlgorithmStatus)
updateAlgorithmStatusByDefaultReset sh = updateAlgorithmStatus sh setDefault
    where
    setDefault :: AlgorithmStatus -> AlgorithmStatus
    setDefault _ = initialAlgorithmStatus


$(makeAcidic ''AppStatus ['logInUser
                          ,'logOutUser
                          ,'peekAppStatus
                          ,'updateAlgorithmStatusByKBC
                          ,'updateAlgorithmStatusByAddingRule 
                          ,'updateAlgorithmStatusByAddingAxiom 
                          ,'updateAlgorithmStatusByRemovingRules
                          ,'updateAlgorithmStatusByRemovingAxioms
                          ,'updateAlgorithmStatusByDefaultReset 
                          ,'checkHashUser])
