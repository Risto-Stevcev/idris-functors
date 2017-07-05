module Test.Functors

import Test.Assert
import Data.Bifunctor

foo : Either String Int
foo = Right 123

bar : Either String Int
bar = Left "hi"

fooIdentity : IO ()
fooIdentity = assertEq "`foo` satisfies the identity property" (bimap id id foo) foo

fooComposition : IO ()
fooComposition = assertEq "`foo` satisfies the composition property"
  (bimap id (show . (+ 3)) foo) ((bimap id show . bimap id (+ 3)) foo)

barIdentity : IO ()
barIdentity = assertEq "`bar` satisfies the identity property" (bimap id id bar) bar

barComposition : IO ()
barComposition = assertEq "`bar` satisfies the composition property"
  (bimap ((++ "!") . (++ "there")) id bar) ((bimap (++ "!") id . bimap (++ "there") id) bar)

fooRmap : IO ()
fooRmap = assertEq "`rmap (+ 3) foo` returns `Right 126`" (rmap (+ 3) foo) (Right 126)

fooLmap : IO ()
fooLmap = assertEq "`lmap` has no effect on a `Right` value" (lmap (++ "!") foo) foo

barRmap : IO ()
barRmap = assertEq "`rmap` has no effect on a `Left` value" (rmap (+ 3) bar) bar

barLmap : IO ()
barLmap = assertEq "`lmap (++ \"!\") bar` returns `Left \"hi!\"`" (lmap (++ "!") bar) (Left "hi!")

export
main : IO ()
main = do
  putStrLn "Testing Bifunctor..."
  fooIdentity
  fooComposition
  barIdentity
  barComposition
  fooRmap
  fooLmap
  barRmap
  barLmap
  putStrLn "Done.\n"
