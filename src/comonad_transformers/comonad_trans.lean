import comonad_transformers.comonad

class comonad_trans (t : (Type → Type) → Type → Type) :=
(lower {w : Type → Type} [comonad w] {a : Type} : t w a → w a)