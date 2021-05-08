import comonad_transformers.comonad
import comonad_transformers.comonad_trans
import monad_transformers.monad_trans

----------------------------
-- Definition + instances --
----------------------------

structure IdentityT (m : Type → Type) (a : Type) := (run : m a)

open IdentityT

instance {m : Type → Type} [functor m] : functor (IdentityT m) := {
  map := λ α β f idntt, mk $ f <$> idntt.run
}

instance {m : Type → Type} [has_pure m] : has_pure (IdentityT m) := {
  pure := λ α a, mk $ pure a
}

instance {m : Type → Type} [has_seq m] : has_seq (IdentityT m) := {
  seq := λ α β idnttab idntta, mk $ idnttab.run <*> idntta.run
}

instance {m : Type → Type} [applicative m] : applicative (IdentityT m) := {}

instance {m : Type → Type} [has_bind m] : has_bind (IdentityT m) := {
  bind := λ α β idntt f, mk $ do a ← idntt.run, (f a).run
}

instance {m : Type → Type} [monad m] : monad (IdentityT m) := {}

instance {m : Type → Type} [has_orelse m] : has_orelse (IdentityT m) := {
  orelse := λ α idntt1 idntt2, mk $ idntt1.run <|> idntt2.run
}

instance {m : Type → Type} [alternative m] : alternative (IdentityT m) := {
  failure := λ α, mk failure
}

protected def IdentityT_lift {m : Type → Type} [monad m] {a : Type} : m a → IdentityT m a :=
λ ma, mk $ ma

instance : monad_trans IdentityT := ⟨@IdentityT_lift⟩

instance {w : Type → Type} [has_extract w] : has_extract (IdentityT w) := {
  extract := λ α idntt, *idntt.run
}

instance {w : Type → Type} [has_extend w] : has_extend (IdentityT w) := {
  extend := λ α β f idntt, mk $ (<<=) _ _ (f ∘ mk) idntt.run
}

instance {w : Type → Type} [comonad w] : comonad (IdentityT w) := {}

protected def IdentityT_lower {w : Type → Type} [comonad w] {a : Type} : IdentityT w a → w a :=
λ idntt, idntt.run

instance : comonad_trans IdentityT := ⟨@IdentityT_lower⟩