{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings,CPP, DeriveDataTypeable, FlexibleContexts, GeneralizedNewtypeDeriving, 
    MultiParamTypeClasses, TemplateHaskell, TypeFamilies, RecordWildCards  #-}
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

data Command = LogIn | LogOut | RunAlgorithm | AddAxiom | RemoveAxiom | RemoveAllAxioms | RemoveRule | RemoveAllRules
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


dispatchPostCommand :: AcidState AppStatus -> ServerPart Response
dispatchPostCommand acid = 
    do methodM POST
       c <- getDataFn (look "command" `checkRq` eitherize)
       case c of
         (Left e) -> (ok $ toResponse $ show (unlines e))
         (Right LogIn) -> (authenticate acid)
         (Right LogOut) -> (deauthenticate acid)
    where
    eitherize :: String -> Either String Command
    eitherize "LogIn" = Right LogIn
    eitherize "LogOut" = Right LogOut
    eitherize r = Left r


authenticate :: AcidState AppStatus -> ServerPart Response
authenticate acid =
     do methodM POST
        l <- look "login"
        p <- look "password"
        x <- liftIO (getStdRandom (randomR (1,65536)))
        result <- update' acid (LogInUser l p (SessionHash (show (x::Integer))))
	case result of
          SuccesfulLogIn sh -> do
             addCookie Session (mkCookie "hash" (hash sh))
             ok $ toResponse (show "User logged in"++(show sh))
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


runKBC:: AcidState AlgorithmStatus -> ServerPart Response
runKBC acid =
    do status <- update' acid (UpdateAlgorithmStatusByKBC)
       showStatus status


showStatus :: AlgorithmStatus -> ServerPart Response
showStatus status =
    do (liftIO $ (generateStatusDiagram (translateName fileName) status))
       serveFile (asContentType "image/png") (translateName fileName)

