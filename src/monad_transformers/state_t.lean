import monad_transformers.monad_trans

----------------------------
-- Definition + instances --
----------------------------

structure StateT (s : Type) (m : Type → Type) (a : Type) := (run : s → m (a × s))

open StateT

instance {s : Type} {m : Type → Type} [functor m] : functor (StateT s m) := {
  map := λ α β f stt, mk $ λ s, (λ p, ⟨f (prod.fst p), prod.snd p⟩) <$> stt.run s
}

instance {s : Type} {m : Type → Type} [has_pure m] : has_pure (StateT s m) := {
  pure := λ α a, mk $ λ s, pure (prod.mk a s)
}

instance {s : Type} {m : Type → Type} [monad m] : has_seq (StateT s m) := {
  seq := λ α β sttab stta, mk $ λ s, sttab.run s >>= λ abs, 
                                stta.run abs.snd >>= λ as, pure ⟨abs.fst as.fst, as.snd⟩
}

instance {s : Type} {m : Type → Type} [monad m] : applicative (StateT s m) := {}

instance {s : Type} {m : Type → Type} [has_bind m] : has_bind (StateT s m) := {
  bind := λ α β stt f, mk $ λ s, stt.run s >>= λ p, (f p.fst).run p.snd
}

instance {s : Type} {m : Type → Type} [monad m] : monad (StateT s m) := {}

instance {s : Type} {m : Type → Type} [has_orelse m] : has_orelse (StateT s m) := {
  orelse := λ α stt1 stt2, mk $ λ s, stt1.run s <|> stt2.run s
}

instance {s : Type} {m : Type → Type} [monad m] [alternative m] : alternative (StateT s m) := {
  failure := λ α, mk $ λ _, failure
}

protected def StateT_lift {s : Type}
                          {m : Type → Type} [monad m]
                          {a : Type} : m a → StateT s m a := λ ma, mk $ λ s, do a ← ma, pure ⟨a, s⟩

instance {s : Type} : monad_trans (StateT s) := ⟨@StateT_lift s⟩