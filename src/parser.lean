----------------------------
-- Definition + instances --
----------------------------

structure Parser (s a : Type) : Type := (run : list s → option (a × list s))

open Parser

instance Parser_functor {s : Type} : functor (Parser s) := {
  map := λ α β f p, 
         mk (λ l, 
             match p.run l with
             | none := none
             | some ⟨a, lst⟩ := some ⟨f a, lst⟩ 
             end)
}

instance Parser_has_pure {s : Type} : has_pure (Parser s) := {
  pure := λ α a, mk (λ lst, some ⟨a, lst⟩)
}

instance Parser_has_seq {s : Type} : has_seq (Parser s) := {
  seq := λ α β pab pa, 
         mk (λ l, 
             match pab.run l with
             | none := none
             | some ⟨ab, l'⟩ := match pa.run l' with
                               | none := none
                               | some ⟨a, l''⟩ := some ⟨ab a, l''⟩
                               end
             end)
}

instance Parser_applicative {s : Type} : applicative (Parser s) := {}

instance Parser_has_bind {s : Type} : has_bind (Parser s) := {
  bind := λ α β p f, mk (λ l, match p.run l with
                              | none := none
                              | some ⟨a, l'⟩ := (f a).run l'
                              end)
}

instance Parser_monad {s : Type} : monad (Parser s) := {}

instance Parser_has_orelse {s : Type} : has_orelse (Parser s) := {
  orelse := λ α p q, mk (λ l, match p.run l with
                        | none := q.run l
                        | some ⟨a, l'⟩ := some ⟨a, l'⟩
                        end)
}

instance Parser_alternative {s : Type} : alternative (Parser s) := {
  failure := λ α, mk (λ l, none)
}

---------------------
-- Extra functions --
---------------------

def evalParser {s a : Type} : Parser s a → list s → option a := 
λ p l, prod.fst <$> p.run l

def execParser {s a : Type} : Parser s a → list s → option (list s) := 
λ p l, prod.snd <$> p.run l

-----------------------
-- Basic combinators --
-----------------------

def ok {s : Type} : Parser s unit := pure ()

def eof {s : Type} : Parser s unit := 
mk $ λ l, match l with
          | [] := some ⟨(), []⟩
          | _ := none
          end

def satisfy {s : Type} (predicate : s → bool) : Parser s s :=
mk $ λ l, match l with 
          | [] := none
          | (x :: xs) := cond (predicate x) (some ⟨x, xs⟩) none 
          -- if ... then ... else ... works too
          end

#eval (satisfy (λ (n : nat), n = 0) >> satisfy (λ (n : nat), n = 0)).run ([0, 0])

def element {s : Type} [decidable_eq s] (c : s) : Parser s s := satisfy (λ d, d = c)

def stream {s : Type} [decidable_eq s] : list s → Parser s (list s)
| [] := pure []
| (x :: xs) := do x' ← element x , xs' ← stream xs, pure (x' :: xs')

#eval (stream "Enter".data).run "Enter Shikari".data
