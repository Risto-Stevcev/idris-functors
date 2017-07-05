module Data.Functor.Coproduct

import Data.Bifunctor
import Control.Comonad

%access public export

-- | `Coproduct f g` is the coproduct of two functors `f` and `g`
data Coproduct : (f : Type -> Type) -> (g : Type -> Type) -> (a : Type) -> Type where
  MkCoproduct : Either (f a) (g a) -> Coproduct f g a


--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

-- | Left injection
left : f a -> Coproduct f g a
left fa = MkCoproduct (Left fa)

-- | Right injection
right : g a -> Coproduct f g a
right ga = MkCoproduct (Right ga)

-- | Eliminate a coproduct by providing eliminators for the left and
-- | right components
eliminate : (f a -> b) -> (g a -> b) -> Coproduct f g a -> b
eliminate f _ (MkCoproduct (Left a)) = f a
eliminate _ g (MkCoproduct (Right b)) = g b

-- | Change the underlying functors in a coproduct
bihoistCoproduct : (Functor f, Functor g, Functor h, Functor i) =>
                   ({a : Type} -> f a -> h a) ->
                   ({a : Type} -> g a -> i a) ->
                   ({a : Type} -> Coproduct f g a -> Coproduct h i a)
bihoistCoproduct natF natG (MkCoproduct e) = MkCoproduct (bimap natF natG e)


--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------

(Eq (f a), Eq (g a)) => Eq (Coproduct f g a) where
  (MkCoproduct fa) == (MkCoproduct ga) = fa == ga

(Ord (f a), Ord (g a)) => Ord (Coproduct f g a) where
  compare (MkCoproduct x) (MkCoproduct y) =
    assert_total $ case (x, y) of
      (Left fa, Left fa') => compare fa fa'
      (Left _, _)  => LT
      (_, Right _) => GT
      (Right ga, Right ga') => compare ga ga'

(Show (f a), Show (g a)) => Show (Coproduct f g a) where
  show (MkCoproduct x) = "Coproduct (" <+> show x <+> ")"

(Functor f, Functor g) => Functor (Coproduct f g) where
  map f (MkCoproduct e) = MkCoproduct (bimap (map f) (map f) e)

(Comonad f, Comonad g) => Comonad (Coproduct f g) where
  extract = eliminate extract extract

(Foldable f, Foldable g) => Foldable (Coproduct f g) where
  foldr f z = eliminate (foldr f z) (foldr f z)
  foldl f z = eliminate (foldl f z) (foldl f z)

(Traversable f, Traversable g) => Traversable (Coproduct f g) where
  traverse f = eliminate (map (MkCoproduct . Left)  . traverse f)
                         (map (MkCoproduct . Right) . traverse f)
