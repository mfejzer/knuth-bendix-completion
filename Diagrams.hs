module Main where 
{-# LANGUAGE NoMonomorphismRestriction #-}
import Control.Monad
import Control.Monad.Trans (lift, liftIO)
import Data.Tree
import Diagrams.Prelude
import Diagrams.TwoD.Layout.Tree
import Diagrams.Backend.Cairo
import Diagrams.Backend.Cairo.CmdLine
import Diagrams.Backend.Cairo.Internal
import Graphics.Rendering.Diagrams.Core
import Happstack.Server (asContentType, dir, look, nullConf, ok, Response, serveFile, ServerPart, simpleHTTP, toResponse)

t1 = Node 'A' [Node 'B' (map lf "CDE"), Node 'F' [Node 'G' (map lf "HIJ")]]

lf :: Char -> Tree Char
lf x = Node x []

simpleTree tree =
	renderTree ((<> circle 1 # fc white) . text . show)
		(~~)
		(symmLayout' with { slHSep = 4, slVSep = 4 } tree)

translateName :: String -> String
translateName name = name++".png"

saveDiagram diagram name = renderDia Cairo (CairoOptions name (Width 250) PNG) diagram

generate name tree = fst(saveDiagram (simpleTree tree) name)

generatePart :: ServerPart Response
generatePart =
	do 
		name <- look "name"
		(liftIO $ generate (translateName name) t1)
		serveFile (asContentType "image/png") (translateName name)

notImplemented = ok $ toResponse $ "Not implemented yet"
main = simpleHTTP nullConf $ msum [mzero, dir "add_axiom" $ notImplemented, dir "run_one_step" $ notImplemented ,dir "generate" $ generatePart, ok $ toResponse $ "Nothing here"]

