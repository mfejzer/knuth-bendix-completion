module DiagramWrapper where
import Data.Tree
import Diagrams.Prelude
import Diagrams.TwoD.Layout.Tree
import Diagrams.Backend.Cairo
import Diagrams.Backend.Cairo.CmdLine
import Diagrams.Backend.Cairo.Internal
import Graphics.Rendering.Diagrams.Core
import KnuthBendixCompletion.Datatypes


makeTree :: Term -> Tree String
makeTree (Func name args) = Node name (map makeTree args)
makeTree (Var name) = Node name []


renderStandardTree tree =
	renderTree ((<> circle 1 # fc white) . text . show)
		(~~)
		(symmLayout' with { slHSep = 4, slVSep = 4 } tree)

saveDiagram diagram fileName = renderDia Cairo (CairoOptions fileName (Width 250) PNG) diagram

generateTreeDiagram name tree = fst(saveDiagram (renderStandardTree tree) name)


