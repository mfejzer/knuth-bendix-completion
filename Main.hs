{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings,CPP, DeriveDataTypeable, FlexibleContexts, GeneralizedNewtypeDeriving, 
    MultiParamTypeClasses, ScopedTypeVariables, TemplateHaskell, TypeFamilies, RecordWildCards  #-}
module Main where 
import Auth.Datatypes
import Control.Exception    ( bracket )
import Control.Monad (msum)
import Control.Monad.Trans (lift, liftIO)
import Data.Acid            ( AcidState, Query, Update, openLocalState )
import Data.Acid.Advanced   ( query', update' )
import Data.Acid.Local      ( createCheckpointAndClose )
import Data.SafeCopy        ( base, deriveSafeCopy )
import Data.Tree
import DiagramWrapper
{-import Graphics.Rendering.Diagrams.Core -}
import Happstack.Server (addCookie, asContentType, BodyPolicy(..)
			, CookieLife(Session), decodeBody
			, defaultBodyPolicy, dir, expireCookie
			, Method(POST), methodM, mkCookie, nullConf
			, ok, readCookieValue, Response, serveFile
			, ServerPart, simpleHTTP, toResponse)
import Happstack.Server.RqData (RqData, checkRq, getDataFn, look, lookRead) 
import KnuthBendixCompletion.Algorithm
import KnuthBendixCompletion.Datatypes
import KnuthBendixCompletion.Tests
import Parser
import ParserTests
import Persistance
import Text.Blaze			as B
import Text.Blaze.Html4.Strict		as B hiding (map)
import Text.Blaze.Html4.Strict.Attributes as B hiding (dir, label, title)
import System.Random

data Command = LogIn | LogOut | RunAlgorithm | AddAxiom | AddRule | RemoveAxiom | RemoveAllAxioms | RemoveRule | RemoveAllRules | Reset
    deriving (Eq, Ord, Read, Show)

main :: IO ()
main =
    do bracket (openLocalState initialAppStatus)
               (createCheckpointAndClose)
               (\acid ->
                    simpleHTTP nullConf (handlers acid))

myPolicy :: BodyPolicy
myPolicy = (defaultBodyPolicy "/tmp/" 0 1000 1000)

handlers :: AcidState AppStatus -> ServerPart Response
handlers acid =
    do decodeBody myPolicy
       msum [dir "login" $ logInUserResultPart 
            ,dir "logout" $ logOutUserResultPart 
            ,dir "app" $ dispatchPostCommand acid
            ,dir "list" $ listUsers acid
            ]


logInUserResultPart :: ServerPart Response
logInUserResultPart = ok $ toResponse $
    html $ do
      B.head $ do
        title "Login Form"
      B.body $ do
        form ! enctype "multipart/form-data" ! B.method "POST" ! action "/app" $ do
             B.label "login: " >> input ! type_ "text" ! name "login" ! size "10"
             B.label "password: " >> input ! type_ "text" ! name "password" ! size "10"
             input ! type_ "hidden" ! name "command" ! value (B.toValue (show LogIn))
             input ! type_ "submit" ! name "log in"

logOutUserResultPart :: ServerPart Response
logOutUserResultPart = ok $ toResponse $
    html $ do
      B.head $ do
        title "Logout Form"
      B.body $ do
        form ! enctype "multipart/form-data" ! B.method "POST" ! action "/app" $ do
             input ! type_ "hidden" ! name "command" ! value (B.toValue (show LogOut))
             input ! type_ "submit" ! name "log in"

menuResultPart :: ServerPart Response
menuResultPart = ok $ toResponse $
    html $ do
     B.head $ do
        title "Menu"
     B.body $ do
        form ! enctype "multipart/form-data" ! B.method "POST" ! action "/app" $ do
             input ! type_ "hidden" ! name "command" ! value (B.toValue (show RunAlgorithm))
             input ! type_ "submit" ! name "RunAlgorithm" ! value "Run Algorithm"
        br
        form ! enctype "multipart/form-data" ! B.method "POST" ! action "/app" $ do
             B.label "Enter axiom: " >> input ! type_ "text" ! name "axiom" ! size "100"
             input ! type_ "hidden" ! name "command" ! value (B.toValue (show AddAxiom))
             input ! type_ "submit" ! name "AddAxiom" ! value "Add Axiom"
        br
        form ! enctype "multipart/form-data" ! B.method "POST" ! action "/app" $ do
             B.label "Enter reduction rule: " >> input ! type_ "text" ! name "rule" ! size "100"
             input ! type_ "hidden" ! name "command" ! value (B.toValue (show AddRule))
             input ! type_ "submit" ! name "AddRule" ! value "Add Reduction Rule"
        br
        form ! enctype "multipart/form-data" ! B.method "POST" ! action "/app" $ do
             input ! type_ "hidden" ! name "command" ! value (B.toValue (show RemoveAxiom))
             input ! type_ "submit" ! name "RemoveAxiom" ! value "Remove Axiom"
        br
        form ! enctype "multipart/form-data" ! B.method "POST" ! action "/app" $ do
             input ! type_ "hidden" ! name "command" ! value (B.toValue (show RemoveRule))
             input ! type_ "submit" ! name "RemoveRule" ! value "Remove Rule"
        br
        form ! enctype "multipart/form-data" ! B.method "POST" ! action "/app" $ do
             input ! type_ "hidden" ! name "command" ! value (B.toValue (show RemoveAllAxioms))
             input ! type_ "submit" ! name "RemoveAllAxioms" ! value "Remove All Axioms"
        br
        form ! enctype "multipart/form-data" ! B.method "POST" ! action "/app" $ do
             input ! type_ "hidden" ! name "command" ! value (B.toValue (show RemoveAllRules))
             input ! type_ "submit" ! name "RemoveAllRules" ! value "Remove All Rules"
        br
        form ! enctype "multipart/form-data" ! B.method "POST" ! action "/app" $ do
             input ! type_ "hidden" ! name "command" ! value (B.toValue (show Reset))
             input ! type_ "submit" ! name "Reset" ! value "Remove Reset"
        br
        form ! enctype "multipart/form-data" ! B.method "POST" ! action "/app" $ do
             input ! type_ "hidden" ! name "command" ! value (B.toValue (show LogOut))
             input ! type_ "submit" ! name "LogOut" ! value "Log Out"
        br
 

dispatchPostCommand :: AcidState AppStatus -> ServerPart Response
dispatchPostCommand acid = 
    do methodM POST
       c <- getDataFn (look "command" `checkRq` eitherize)
       case c of
            (Left e) -> (ok $ toResponse $ show (unlines e))
            (Right LogIn) -> (authenticate acid)
            (Right LogOut) -> (deauthenticate acid)
            (Right c) -> do hashValue::String <- readCookieValue "hash"
                            isLogged <- query' acid (CheckHashUser (SessionHash hashValue))
                            case isLogged of
                                 UserIsNotLogged -> ok $ toResponse (show "No such user")
                                 UserIsLogged -> generateResult acid c (SessionHash hashValue)
    where
    eitherize :: String -> Either String Command
    eitherize "LogIn" = Right LogIn
    eitherize "LogOut" = Right LogOut
    eitherize "RunAlgorithm" = Right RunAlgorithm
    eitherize "AddAxiom" = Right AddAxiom
    eitherize "AddRule" = Right AddRule
    eitherize "RemoveAxiom" = Right RemoveAxiom 
    eitherize "RemoveRule" = Right RemoveRule 
    eitherize "RemoveAllAxioms" = Right RemoveAllAxioms
    eitherize "RemoveAllRules" = Right RemoveAllRules
    eitherize "Reset" = Right Reset
    eitherize r = Left r


generateResult :: AcidState AppStatus -> Command -> SessionHash -> ServerPart Response
generateResult acid c sh =
    case c of
      RunAlgorithm -> do result <- update' acid (UpdateAlgorithmStatusByKBC sh)
                         case result of
                           Just r -> showStatus r
                           Nothing -> ok $ toResponse (show "Nothing")
      AddAxiom -> do postedAxiom <- getDataFn (look "axiom" `checkRq` (convertError.parseAxiom))
	             case postedAxiom of
			  (Left error) -> (ok $ toResponse $ (show error))
			  (Right axiom) -> do result <- update' acid (UpdateAlgorithmStatusByAddingAxiom sh axiom)
                                              case result of
                                                   Just r -> showStatus r
                                                   Nothing -> ok $ toResponse (show "Nothing")
      AddRule -> do postedRule <- getDataFn (look "rule" `checkRq` (convertError.parseReductionRule))
	            case postedRule of
			  (Left error) -> (ok $ toResponse $ (show error))
			  (Right rule) -> do result <- update' acid (UpdateAlgorithmStatusByAddingRule sh rule)
                                             case result of
                                               Just r -> showStatus r
                                               Nothing -> ok $ toResponse (show "Nothing")
      RemoveRule ->  do ok $ toResponse (show "To implement")
      RemoveAxiom -> do ok $ toResponse (show "To implement")
      RemoveAllAxioms ->do result <- update' acid (UpdateAlgorithmStatusByRemovingAxioms sh)
                           case result of
                             Just r -> showStatus r
                             Nothing -> ok $ toResponse (show "Nothing")
      RemoveAllRules ->do result <- update' acid (UpdateAlgorithmStatusByRemovingRules sh)
                          case result of
                            Just r -> showStatus r
                            Nothing -> ok $ toResponse (show "Nothing")
      Reset-> do result <- update' acid  (UpdateAlgorithmStatusByDefaultReset sh)
                 case result of
                      Just r -> showStatus r
                      Nothing -> ok $ toResponse (show "Nothing")



authenticate :: AcidState AppStatus -> ServerPart Response
authenticate acid =
     do methodM POST
        l <- look "login"
        p <- look "password"
        x <- liftIO (getStdRandom (randomR (1,65536)))
        result <- update' acid (LogInUser l p (SessionHash (l++show (x::Integer))))
	case result of
          SuccesfulLogIn sh -> do
             addCookie Session (mkCookie "hash" (hash sh))
             menuResultPart
          NoSuchUser -> ok $ toResponse (show "No such user")
          WrongPassword -> ok $ toResponse (show "Wrong password")


deauthenticate :: AcidState AppStatus -> ServerPart Response
deauthenticate acid =
     do hashValue::String <- readCookieValue "hash"
        result <- update' acid (LogOutUser (SessionHash hashValue))
        case result of
          SuccesfulLogOut -> do
            expireCookie "hash"
            ok $ toResponse (show "User logged out") 
          NoSuchSessionHash -> ok $ toResponse (show "No user was logged with this cookie "++(show (SessionHash hashValue)))


listUsers :: AcidState AppStatus -> ServerPart Response
listUsers acid = 
    do status <- query' acid PeekAppStatus
       ok $ toResponse $ "peeked and saw: " ++ show (map (\u -> (login u, password u,session u)) (users status))

addAxiomFormPart :: ServerPart Response
addAxiomFormPart = ok $ toResponse $
    html $ do
      B.head $ do
        title "Add Axiom"
      B.body $ do
	form ! enctype "multipart/form-data" ! B.method "POST" ! action "/AddAxiom/Result" $ do
             B.label "Enter axiom: " >> input ! type_ "text" ! name "axiom" ! size "100"
             input ! type_ "submit" ! name "Enter"

addAxiomResultPart :: AcidState AlgorithmStatus -> ServerPart Response
addAxiomResultPart acid =
	do methodM POST 
	   result <- getDataFn (look "axiom" `checkRq` (convertError.parseAxiom))
	   case result of
			(Left error) -> (ok $ toResponse $ (show error))
			(Right axiom) -> do (liftIO $ (generateAxiomDiagram (translateName fileName) axiom))
					    serveFile (asContentType "image/png") (translateName fileName)
translateName :: String -> String
translateName name = name++".png"

fileName = "tmp"

showStatus :: AlgorithmStatus -> ServerPart Response
showStatus status =
    do (liftIO $ (generateStatusDiagram (translateName fileName) status))
       serveFile (asContentType "image/png") (translateName fileName)

