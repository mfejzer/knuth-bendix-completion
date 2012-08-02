module Main where 
{-# LANGUAGE NoMonomorphismRestriction #-}
import Control.Monad
import Control.Monad.Trans (lift, liftIO)
import Data.Tree
import DiagramWrapper (generateTreeDiagram)
import Graphics.Rendering.Diagrams.Core
import Happstack.Server (asContentType, dir, look, nullConf, ok, Response, serveFile, ServerPart, simpleHTTP, toResponse)
import KnuthBendixCompletion.Algorithm
import KnuthBendixCompletion.Datatypes
import KnuthBendixCompletion.Test
import Parser

t1 = Node 'A' [Node 'B' (map lf "CDE"), Node 'F' [Node 'G' (map lf "HIJ")]]

lf :: Char -> Tree Char
lf x = Node x []

translateName :: String -> String
translateName name = name++".png"

generatePart :: ServerPart Response
generatePart =
	do 
		name <- look "name"
		(liftIO $ generateTreeDiagram (translateName name) t1)
		serveFile (asContentType "image/png") (translateName name)

notImplemented = ok $ toResponse $ "Not implemented yet"
main = simpleHTTP nullConf $ msum [mzero, dir "add_axiom" $ notImplemented, dir "run_one_step" $ notImplemented ,dir "generate" $ generatePart, ok $ toResponse $ "Nothing here"]

