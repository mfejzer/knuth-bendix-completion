module DiagramWrapper where
import Data.Tree
import Diagrams.Prelude
import Diagrams.TwoD.Layout.Tree
import Diagrams.TwoD.Text
import Diagrams.Backend.Cairo
import Diagrams.Backend.Cairo.CmdLine
import Diagrams.Backend.Cairo.Internal
import Graphics.Rendering.Diagrams.Core
import KnuthBendixCompletion.Datatypes

renderArgs (axioms,reductionRules) =
    axiomsDiagram === rulesDiagram
    where
    axiomsDiagram = foldl (===) (text "Axioms" <> rect 5 1)  (map renderAxiom axioms)
    rulesDiagram = foldl (===) (text "ReductionRules" <> rect 7 1) (map renderReductionRule reductionRules)


renderReductionRule reductionRule = ((makeAndRender.getRule) reductionRule) ||| (text "->" <> rect 3 1) ||| ((makeAndRender.getResult) reductionRule) 
renderAxiom axiom = ((makeAndRender.lhs) axiom) ||| (text "<->" <> rect 3 1) ||| ((makeAndRender.rhs) axiom) 

makeAndRender term = (renderStandardTree.makeTree) term

makeTree :: Term -> Tree String
makeTree (Func name args) = Node name (map makeTree args)
makeTree (Var name) = Node name []


renderStandardTree tree =
	renderTree ((<> circle 1 # fc white) . text . show)
		(~~)
		(symmLayout' with { slHSep = 2, slVSep = 2 } tree)


saveDiagram diagram fileName = renderDia Cairo (CairoOptions fileName (Width 250) PNG) diagram


generateTreeDiagram name tree = fst(saveDiagram (renderStandardTree tree) name)

generateReductionRuleDiagram name reductionRule = generate name (renderReductionRule reductionRule)
generateAxiomDiagram name axiom = generate name (renderAxiom axiom)

generateArgsDiagram name args = generate name (renderArgs args)

generate name renderer = fst(saveDiagram renderer name)

