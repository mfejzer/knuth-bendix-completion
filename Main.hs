{-module Main where -}
{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings #-}
import Control.Monad (msum)
import Control.Monad.Trans (lift, liftIO)
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
import Text.Blaze			as B
import Text.Blaze.Html4.Strict		as B hiding (map)
import Text.Blaze.Html4.Strict.Attributes as B hiding (dir, label, title)

main :: IO ()
main = simpleHTTP nullConf $ handlers

myPolicy :: BodyPolicy
myPolicy = (defaultBodyPolicy "/tmp/" 0 1000 1000)

handlers :: ServerPart Response
handlers =
    do decodeBody myPolicy
       msum [dir "AddAxiom" $ dir "Form" $ addAxiomFormPart
            ,dir "AddAxiom" $ dir "Result" $ addAxiomResultPart
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

addAxiomResultPart :: ServerPart Response
addAxiomResultPart =
	do methodM POST 
	   result <- getDataFn (look "axiom" `checkRq` (convertError.parseAxiom))
	   case result of
			(Left error) -> (ok $ toResponse $ (show error))
			(Right axiom) -> do (liftIO $ (generateAxiomDiagram (translateName fileName) axiom))
					    serveFile (asContentType "image/png") (translateName fileName)
translateName :: String -> String
translateName name = name++".png"

fileName = "tmp"

