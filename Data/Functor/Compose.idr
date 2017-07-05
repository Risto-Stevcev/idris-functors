module Data.Functor.Compose

%access public export

-- | `Compose f g` is the composition of the two functors `f` and `g`.
data Compose : (f : Type -> Type) -> (g : Type -> Type) -> (a : Type) -> Type where
  MkCompose : f (g a) -> Compose f g a


--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

bihoistCompose : (Functor f, Functor g, Functor h, Functor i) =>
                 ({a : Type} -> f a -> h a) ->
                 ({a : Type} -> g a -> i a) ->
                 ({a : Type} -> Compose f g a -> Compose h i a)
bihoistCompose natF natG (MkCompose fga) = MkCompose (natF (map natG fga))


--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------

Eq (f (g a)) => Eq (Compose f g a) where
  (MkCompose x) == (MkCompose y) = x == y

Ord (f (g a)) => Ord (Compose f g a) where
  compare (MkCompose x) (MkCompose y) = compare x y

Show (f (g a)) => Show (Compose f g a) where
  show (MkCompose x) = "Compose (" <+> show x <+> ")"

(Functor f, Functor g) => Functor (Compose f g) where
  map f (MkCompose fga) = MkCompose $ map f <$> fga

(Applicative f, Applicative g) => Applicative (Compose f g) where
  pure = MkCompose . pure . pure
  (MkCompose x) <*> (MkCompose y) = MkCompose $ map (<*>) x <*> y

(Foldable f, Foldable g) => Foldable (Compose f g) where
  foldr f init (MkCompose fga) = foldr (flip (foldr f)) init fga
  foldl f init (MkCompose fga) = foldl (foldl f) init fga

(Traversable f, Traversable g) => Traversable (Compose f g) where
  traverse f (MkCompose fga) = map MkCompose $ traverse (traverse f) fga

(Alternative f, Applicative g) => Alternative (Compose f g) where
  empty = MkCompose empty
  (MkCompose x) <|> (MkCompose y) = MkCompose (x <|> y)
