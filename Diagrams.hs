{-# LANGUAGE NoMonomorphismRestriction #-}
import Data.Tree
import Diagrams.Prelude
import Diagrams.TwoD.Layout.Tree
import Diagrams.Backend.Cairo
import Diagrams.Backend.Cairo.CmdLine
import Diagrams.Backend.Cairo.Internal
import Graphics.Rendering.Diagrams.Core

t1 = Node 'A' [Node 'B' (map lf "CDE"), Node 'F' [Node 'G' (map lf "HIJ")]]

lf :: Char -> Tree Char
lf x = Node x []

example =
  renderTree ((<> circle 1 # fc white) . text . show)
             (~~)
             (symmLayout' with { slHSep = 4, slVSep = 4 } t1)

combos diagram = renderDia Cairo (CairoOptions "foo.png" (Width 250) PNG) diagram
main = fst(combos example)
