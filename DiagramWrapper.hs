{-# LANGUAGE NoMonomorphismRestriction, OverloadedStrings,CPP, DeriveDataTypeable, FlexibleContexts, GeneralizedNewtypeDeriving #-}

module DiagramWrapper where
import Data.Tree
import Diagrams.Prelude
import Diagrams.TwoD.Layout.Tree
import Diagrams.TwoD.Text
import Diagrams.Size
import Diagrams.Backend.Cairo
import Diagrams.Backend.Cairo.CmdLine
import Diagrams.Backend.Cairo.Internal
import Diagrams.Core.Types
import KnuthBendixCompletion.Datatypes

renderStatus CanProceed {axioms=currentAxioms,rules=currentRules} =
    (axiomsDiagram currentAxioms)===(rulesDiagram currentRules)
renderStatus Finished {finalRules=currentRules} =
    (rulesDiagram currentRules)
renderStatus FailedOn {lastAxiom=axiom,incompleteAxioms=currentAxioms,incompleteRules=currentRules} =
    (renderAxiom axiom)===(axiomsDiagram currentAxioms)===(rulesDiagram currentRules)
    
axiomsDiagram currentAxioms = foldl (===) (text "Axioms" <> rect 5 1)  (map renderAxiom currentAxioms)
rulesDiagram currentReductionRules = foldl (===) (text "ReductionRules" <> rect 7 1) (map renderReductionRule currentReductionRules)


renderReductionRule reductionRule = ((makeAndRender.rule) reductionRule) ||| (text "->" <> rect 3 1) ||| ((makeAndRender.result) reductionRule) 
renderAxiom axiom = ((makeAndRender.lhs) axiom) ||| (text "<->" <> rect 3 1) ||| ((makeAndRender.rhs) axiom) 

makeAndRender term = (renderStandardTree.makeTree) term

makeTree :: Term -> Tree String
makeTree (Func name args) = Node name (map makeTree args)
makeTree (Var name) = Node name []


renderStandardTree tree =
	renderTree ((<> circle 1 # fc white) . text . show)
		(~~)
		(symmLayout' (with & slHSep .~ 2 & slVSep .~ 2) tree)


saveDiagram diagram fileName = renderDia Cairo (CairoOptions fileName (mkWidth 250) PNG False) diagram


generateTreeDiagram name tree = fst(saveDiagram (renderStandardTree tree) name)

generateReductionRuleDiagram name reductionRule = generate name (renderReductionRule reductionRule)
generateAxiomDiagram name axiom = generate name (renderAxiom axiom)

generateStatusDiagram name status = generate name (renderStatus status)

generate name renderer = fst(saveDiagram renderer name)

