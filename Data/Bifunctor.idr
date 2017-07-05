module Data.Bifunctor

%access public export

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

interface Bifunctor (f : Type -> Type -> Type) where
  bimap : (a -> b) -> (c -> d) -> f a c -> f b d

interface Bifunctor f => VerifiedBifunctor (f : Type -> Type -> Type) where
  bifunctorIdentity : {a, b : Type} -> (x : f a b) -> bimap Basics.id Basics.id x = Basics.id x
  bifunctorComposition : {a, b, c, d, e, g : Type} -> (x : f a b) ->
                         (f1 : a -> c) -> (f2 : c -> d) ->
                         (g1 : b -> e) -> (g2 : e -> g) ->
                         bimap (f2 . f1) (g2 . g1) x = (bimap f2 g2 . bimap f1 g1) x


--------------------------------------------------------------------------------
-- Implementations
--------------------------------------------------------------------------------

Bifunctor Either where
  bimap f _ (Left l) = Left (f l)
  bimap _ g (Right r) = Right (g r)

VerifiedBifunctor Either where
  bifunctorIdentity (Left l) = Refl
  bifunctorIdentity (Right r) = Refl
  bifunctorComposition (Left l) f1 f2 g1 g2 = Refl
  bifunctorComposition (Right r) f1 f2 g1 g2 = Refl

Bifunctor Pair where
  bimap f g (a, b) = (f a, g b)

VerifiedBifunctor Pair where
  bifunctorIdentity (a, b) = Refl
  bifunctorComposition (a, b) f1 f2 g1 g2 = Refl


--------------------------------------------------------------------------------
-- Functions
--------------------------------------------------------------------------------

-- | Map a function over the first type argument of a `Bifunctor`.
lmap : Bifunctor f => (a -> b) -> f a c -> f b c
lmap f = bimap f id

-- | Map a function over the second type arguments of a `Bifunctor`.
rmap : Bifunctor f => (b -> c) -> f a b -> f a c
rmap = bimap id
