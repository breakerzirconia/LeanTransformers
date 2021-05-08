import algebra.group
import comonad_transformers.comonad
import comonad_transformers.comonad_trans

----------------------------
-- Definition + instances --
----------------------------

structure TracedT (t : Type) (w : Type → Type) (a : Type) := (run : w (t → a))

open TracedT

instance {t : Type} {w : Type → Type} [functor w] : functor (TracedT t w) := {
  map := λ α β f trcd, mk $ (λ g, f ∘ g) <$> trcd.run
}

instance {t : Type} [monoid t] {w : Type → Type} [has_extract w] : has_extract (TracedT t w) := {
  extract := λ α trcd, (*trcd.run) 1
}

instance {t : Type} [monoid t] {w : Type → Type} [functor w] [has_extend w] : has_extend (TracedT t w) := {
  extend := λ α β f trcd, mk $ (<<=) _ _ (λ wta tt, 
                                          f (mk $ (λ (g : t → α) tt', g (tt * tt')) <$> wta)) trcd.run
}

instance {t : Type} [monoid t] {w : Type → Type} [comonad w] : comonad (TracedT t w) := {}

protected def TracedT_lower {t : Type} [has_one t]
                            {w : Type → Type} [comonad w]
                            {a : Type} : TracedT t w a → w a := λ trcd, (λ (f : t → a), f 1) <$> trcd.run

instance {t : Type} [has_one t] : comonad_trans (TracedT t) := ⟨@TracedT_lower t _⟩