{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings,CPP, DeriveDataTypeable, FlexibleContexts, GeneralizedNewtypeDeriving, 
    MultiParamTypeClasses, TemplateHaskell, TypeFamilies, RecordWildCards  #-}
module Main where 
import Control.Exception    ( bracket )
import Control.Monad (msum)
import Control.Monad.Trans (lift, liftIO)
import Data.Acid            ( AcidState, Query, Update, openLocalState )
import Data.Acid.Advanced   ( query', update' )
import Data.Acid.Local      ( createCheckpointAndClose )
import Data.SafeCopy        ( base, deriveSafeCopy )
import Data.Tree
import DiagramWrapper
import Graphics.Rendering.Diagrams.Core 
import Happstack.Server (asContentType, BodyPolicy(..), decodeBody, defaultBodyPolicy, dir
			, nullConf, ok, Method(POST), methodM, Response, serveFile
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

main :: IO ()
main =
    do bracket (openLocalState initialArgsState)
               (createCheckpointAndClose)
               (\acid ->
                    simpleHTTP nullConf (handlers acid))

myPolicy :: BodyPolicy
myPolicy = (defaultBodyPolicy "/tmp/" 0 1000 1000)

handlers :: AcidState ArgsState -> ServerPart Response
handlers acid =
    do decodeBody myPolicy
       msum [dir "AddAxiom" $ dir "Form" $ addAxiomFormPart
            ,dir "AddAxiom" $ dir "Result" $ addAxiomResultPart acid
            ,dir "RunKBC" $ runKBC acid
            , do args <- query' acid PeekArgs 
                 showArgs args
            ]


addAxiomFormPart :: ServerPart Response
addAxiomFormPart = ok $ toResponse $
    html $ do
      B.head $ do
        title "Add Axiom"
      B.body $ do
	form ! enctype "multipart/form-data" ! B.method "POST" ! action "/AddAxiom/Result" $ do
             B.label "Enter axiom: " >> input ! type_ "text" ! name "axiom" ! size "100"
             input ! type_ "submit" ! name "Enter"

addAxiomResultPart :: AcidState ArgsState -> ServerPart Response
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


runKBC:: AcidState ArgsState -> ServerPart Response
runKBC acid =
    do args <- update' acid (UpdateArgsByKBC)
       showArgs args


showArgs :: (Axioms,ReductionRules) -> ServerPart Response
showArgs args =
    do (liftIO $ (generateArgsDiagram (translateName fileName) args))
       serveFile (asContentType "image/png") (translateName fileName)

