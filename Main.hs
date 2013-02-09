{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings,CPP, DeriveDataTypeable, FlexibleContexts, GeneralizedNewtypeDeriving, 
    MultiParamTypeClasses, ScopedTypeVariables, TemplateHaskell, TypeFamilies, RecordWildCards  #-}
module Main where 
import Auth.Datatypes
import Control.Exception    ( bracket )
import Control.Monad (msum,mapM_,forM_,forM)
import Control.Monad.Trans (lift, liftIO)
import Data.Acid            ( AcidState, Query, Update, openLocalState )
import Data.Acid.Advanced   ( query', update' )
import Data.Acid.Local      ( createCheckpointAndClose )
import Data.SafeCopy        ( base, deriveSafeCopy )
import Data.Tree
import DiagramWrapper
import Happstack.Server (addCookie, asContentType, BodyPolicy(..)
			, Browsing(EnableBrowsing), CookieLife(Session)
                        , decodeBody, defaultBodyPolicy, dir, expireCookie
			, Method(POST), methodM, mkCookie, nullConf
			, ok, readCookieValue, Response, serveDirectory
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
            ,dir "img" $ serveDirectory EnableBrowsing [] "img"
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
        menu

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

translateName :: String -> String
translateName name = "img/"++name++".png"

showStatus :: AlgorithmStatus -> ServerPart Response
showStatus (CanProceed as rs) =
    do axiomsFilenames <- mapM generateAxiomAsImage (numberize as)
       rulesFilenames <- mapM generateRuleAsImage (numberize rs)
       canProceedTemplate axiomsFilenames rulesFilenames
    

numberize xs = n xs 0
    where
    n [] _ = []
    n (x:xs) acc = (x,acc): n xs (acc+1)

canProceedTemplate :: [(String,Integer)] -> [(String,Integer)] ->  ServerPart Response
canProceedTemplate axiomsFilenames rulesFilenames = ok $ toResponse $
    html $ do
      B.head $ do
        title "Algorithm Status"
      B.body $ do 
          ul $ forM_ axiomsFilenames (htmlize RemoveAxiom)
          ul $ forM_ rulesFilenames (htmlize RemoveRule)
          menu

htmlize removeCommand (filename,index) = 
    do li $ form ! enctype "multipart/form-data" ! B.method "POST" ! action "/app" $ do
             img ! src (B.toValue filename)
             input ! type_ "hidden" ! name "command" ! value (B.toValue (show removeCommand))
             input ! type_ "hidden" ! name "index" ! value (B.toValue (show index))
             input ! type_ "submit" ! name "Remove" ! value "Remove"
       br


menu=do form ! enctype "multipart/form-data" ! B.method "POST" ! action "/app" $ do
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
 

randomFilename =
    do x <- liftIO (getStdRandom (randomR (1,65536)))
       let filename = (translateName (show (x::Integer)))
       return filename 

generateAxiomAsImage (axiom,index) =
    do filename <- randomFilename
       liftIO $ (generateAxiomDiagram filename axiom)
       return $ (filename,index)
       

generateRuleAsImage (rule,index) =
    do filename <- randomFilename
       liftIO $ generateReductionRuleDiagram filename rule
       return $ (filename,index)

