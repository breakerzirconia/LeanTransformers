import algebra.group
import monad_transformers.monad_trans

----------------------------
-- Definition + instances --
----------------------------

structure WriterT (w : Type) (m : Type → Type) (a : Type) := (run : m (a × w))

open WriterT

instance {w : Type} {m : Type → Type} [functor m] : functor (WriterT w m) := {
  map := λ α β f wrtr, mk $ (λ p, prod.mk (f (prod.fst p)) p.snd) <$> wrtr.run
}

instance {w : Type} [has_one w] {m : Type → Type} [has_pure m] : has_pure (WriterT w m) := {
  pure := λ α a, mk $ pure ⟨a, 1⟩
}

instance {w : Type} [has_mul w] {m : Type → Type} [functor m] [has_seq m] : has_seq (WriterT w m) := {
  seq := λ α β wrtrab wrtra, mk $ (λ (abw : (α → β) × w) (aw : α × w), 
                                   ⟨(abw.fst) (aw.fst), (abw.snd) * (aw.snd)⟩) <$> wrtrab.run 
                                                                              <*> wrtra.run
}

instance {w : Type} [monoid w] {m : Type → Type} [applicative m] : applicative (WriterT w m) := {}

instance {w : Type} [monoid w] {m : Type → Type} [monad m] : has_bind (WriterT w m) := {
  bind := λ α β wrtr f, mk $ wrtr.run >>= λ p, 
                        (f p.fst).run >>= λ p', pure ⟨p'.fst, p.snd * p'.snd⟩
}

instance {w : Type} [monoid w] {m : Type → Type} [monad m] : monad (WriterT w m) := {}

protected def WriterT_lift {w : Type} [has_one w]
                           {m : Type → Type} [monad m] 
                           {a : Type} : m a → WriterT w m a := λ ma, mk $ do a ← ma, pure ⟨a, 1⟩

instance {w : Type} [has_one w] : monad_trans (WriterT w) := ⟨@WriterT_lift w _⟩