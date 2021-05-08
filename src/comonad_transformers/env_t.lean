import comonad_transformers.comonad
import comonad_transformers.comonad_trans

----------------------------
-- Definition + instances --
----------------------------

structure EnvT (e : Type) (w : Type → Type) (a : Type) := (env : e) (val : w a)

open EnvT

instance {e : Type} {w : Type → Type} [functor w] : functor (EnvT e w) := {
  map := λ α β f env, mk env.env (f <$> env.val)
}

instance {e : Type} {w : Type → Type} [has_extract w] : has_extract (EnvT e w) := {
  extract := λ α env, *env.val
}

instance {e : Type} {w : Type → Type} [functor w] [has_extend w] : has_extend (EnvT e w) := {
  extend := λ α β f env, mk env.env (f <$> (<<=) _ _ (mk env.env) env.val)
}

instance {e : Type} {w : Type → Type} [comonad w] : comonad (EnvT e w) := {}

protected def EnvT_lower {e : Type}
                         {w : Type → Type} [comonad w]
                         {a : Type} : EnvT e w a → w a := λ env, env.val

instance {e : Type} : comonad_trans (EnvT e) := ⟨@EnvT_lower e⟩