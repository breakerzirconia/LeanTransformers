class has_extract (w : Type → Type) := 
(extract {α : Type} : w α → α)

prefix ` * `:100 := has_extract.extract

class has_extend (w : Type → Type) :=
(extend : Π α β : Type, (w α → β) → w α → w β)

infix ` <<= `:55 := has_extend.extend 

infix ` =>> `:55 := flip has_extend.extend 

class comonad (w : Type → Type) extends functor w, has_extract w, has_extend w

@[inline] def comonad.duplicate {α : Type} {w : Type → Type} [has_extend w] : w α → w (w α) := (<<=) _ _ id

prefix ` & `:100 := comonad.duplicate 