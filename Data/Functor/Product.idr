module Data.Functor.Product

import Data.Bifunctor
import Control.Comonad

%access public export

-- | `Product f g` is the product of the two functors `f` and `g`.
data Product : (f : Type -> Type) -> (g : Type -> Type) -> (a : Type) -> Type where
  MkProduct : (f a, g a) -> Product f g a


--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

product : f a -> g a -> Product f g a
product fa ga = MkProduct (fa, ga)

unwrapProduct : Product f g a -> (f a, g a)
unwrapProduct (MkProduct x) = x

bihoistProduct : (Functor f, Functor g, Functor h, Functor i) =>
                 ({a : Type} -> f a -> h a) ->
                 ({a : Type} -> g a -> i a) ->
                 ({a : Type} -> Product f g a -> Product h i a)
bihoistProduct natF natG (MkProduct e) = MkProduct (bimap natF natG e)


--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------

(Eq (f a), Eq (g a)) => Eq (Product f g a) where
  (MkProduct x) == (MkProduct y) = x == y

(Ord (f a), Ord (g a)) => Ord (Product f g a) where
  compare (MkProduct (l1, r1)) (MkProduct (l2, r2)) =
    case compare l1 l2 of
      EQ => compare r1 r2
      o => o

(Show (f a), Show (g a)) => Show (Product f g a) where
  show (MkProduct x) = "Product (" <+> show x <+> ")"

(Functor f, Functor g) => Functor (Product f g) where
  map f (MkProduct e) = MkProduct (bimap (map f) (map f) e)

(Applicative f, Applicative g) => Applicative (Product f g) where
  pure x = product (pure x) (pure x)
  (MkProduct (f, g)) <*> (MkProduct (a, b)) = product (f <*> a) (g <*> b)

(Monad f, Monad g) => Monad (Product f g) where
  (MkProduct (fa, ga)) >>= f =
    product (fa >>= fst . unwrapProduct . f) (ga >>= snd . unwrapProduct . f)

(Foldable f, Foldable g) => Foldable (Product f g) where
  foldr f z (MkProduct (fa, ga)) = foldr f (foldr f z ga) fa
  foldl f z (MkProduct (fa, ga)) = foldl f (foldl f z fa) ga

(Traversable f, Traversable g) => Traversable (Product f g) where
  traverse f (MkProduct (fa, ga)) = liftA2 product (traverse f fa) (traverse f ga)
