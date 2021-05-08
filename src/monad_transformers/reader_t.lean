import monad_transformers.monad_trans

----------------------------
-- Definition + instances --
----------------------------

structure ReaderT (r : Type) (m : Type → Type) (a : Type) := (run : r → m a)

open ReaderT

instance {r : Type} {m : Type → Type} [functor m] : functor (ReaderT r m) := {
  map := λ α β f rdr, mk $ functor.map f ∘ rdr.run
}

instance {r : Type} {m : Type → Type} [has_pure m] : has_pure (ReaderT r m) := {
  pure := λ α a, mk $ λ _, pure a
}

instance {r : Type} {m : Type → Type} [has_seq m] : has_seq (ReaderT r m) := {
  seq := λ α β rdrab rdra, mk $ λ r, rdrab.run r <*> rdra.run r
}

instance {r : Type} {m : Type → Type} [applicative m] : applicative (ReaderT r m) := {}

instance {r : Type} {m : Type → Type} [has_bind m] : has_bind (ReaderT r m) := {
  bind := λ α β rdr f, mk $ λ r, rdr.run r >>= λ a, (f a).run r
}

instance {r : Type} {m : Type → Type} [monad m] : monad (ReaderT r m) := {}

instance {r : Type} {m : Type → Type} [has_orelse m] : has_orelse (ReaderT r m) := {
  orelse := λ α rdr1 rdr2, mk $ λ r, rdr1.run r <|> rdr2.run r
}

instance {r : Type} {m : Type → Type} [alternative m] : alternative (ReaderT r m) := {
  failure := λ α, mk $ λ r, failure
}

protected def ReaderT_lift {r : Type}
                           {m : Type → Type} [monad m] 
                           {a : Type} : m a → ReaderT r m a := λ ma, mk $ λ _, ma

instance {r : Type} : monad_trans (ReaderT r) := ⟨@ReaderT_lift r⟩