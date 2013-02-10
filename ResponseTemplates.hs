{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings,CPP, DeriveDataTypeable, FlexibleContexts, GeneralizedNewtypeDeriving, 
    MultiParamTypeClasses, ScopedTypeVariables, TemplateHaskell, TypeFamilies, RecordWildCards  #-}
module ResponseTemplates where
import Commands
import Control.Monad (msum,mapM_,forM_,forM)
import Happstack.Server (ok, Response, ServerPart, toResponse)
import KnuthBendixCompletion.Datatypes
import Text.Blaze			as B
import Text.Blaze.Html4.Strict		as B hiding (map)
import Text.Blaze.Html4.Strict.Attributes as B hiding (dir, label, title)


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

canProceedTemplate :: [(String,Integer)] -> [(String,Integer)] ->  ServerPart Response
canProceedTemplate axiomsFilenames rulesFilenames = ok $ toResponse $
    html $ do
      B.head $ do
        title "Algorithm Status"
      B.body $ do 
          ul $ forM_ axiomsFilenames (htmlize RemoveAxiom)
          ul $ forM_ rulesFilenames (htmlize RemoveRule)
          menu

finishedTemplate :: [(String,Integer)] -> ServerPart Response
finishedTemplate rulesFilenames = ok $ toResponse $ 
    html $ do
      B.head $ do
        title "Algorithm Status"
      B.body $ do 
          ul $ forM_ rulesFilenames (display)
          menu

failedOnTemplate :: (String,Integer) -> [(String,Integer)] -> [(String,Integer)] ->  ServerPart Response
failedOnTemplate failedAxiomFilename axiomsFilenames rulesFilenames = ok $ toResponse $ 
    html $ do
      B.head $ do
        title "Algorithm Status"
      B.body $ do 
          display failedAxiomFilename
          ul $ forM_ axiomsFilenames (display)
          ul $ forM_ rulesFilenames (display)
          menu

display (filename,_) =
    do li $ img ! src (B.toValue filename)
       br

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
 
