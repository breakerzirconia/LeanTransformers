class monad_trans (t : (Type → Type) → Type → Type) :=
(lift {m : Type → Type} [monad m] {a : Type} : m a → t m a)