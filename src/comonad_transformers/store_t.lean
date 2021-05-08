import comonad_transformers.comonad
import comonad_transformers.comonad_trans

----------------------------
-- Definition + instances --
----------------------------

structure StoreT (s : Type) (w : Type → Type) (a : Type) := (func : w (s → a)) (sval : s)

open StoreT

instance {s : Type} {w : Type → Type} [functor w] : functor (StoreT s w) := {
  map := λ α β f str, mk ((λ g, f ∘ g) <$> str.func) str.sval
}

instance {s : Type} {w : Type → Type} [has_extract w] : has_extract (StoreT s w) := {
  extract := λ α str, (*str.func) str.sval
}

instance {s : Type} {w : Type → Type} [has_extend w] : has_extend (StoreT s w) := {
  extend := λ α β f str, mk ((<<=) _ _ (λ wsa s, f (mk wsa s)) str.func) str.sval
}

instance {s : Type} {w : Type → Type} [comonad w] : comonad (StoreT s w) := {}

protected def StoreT_lower {s : Type}
                           {w : Type → Type} [comonad w]
                           {a : Type} : StoreT s w a → w a := λ str, (λ (f : s → a), f str.sval) <$> str.func

instance {s : Type} : comonad_trans (StoreT s) := ⟨@StoreT_lower s⟩