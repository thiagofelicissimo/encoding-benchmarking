constant symbol END : TYPE;
constant symbol ■ : END;

constant symbol Type : TYPE;
injective symbol El : Type → TYPE;

constant symbol ⇝ : Type → Type → Type;
notation ⇝ infix right 7;
constant symbol abs [A B : Type] : (El A → El B) → El (A ⇝ B);
symbol app [A B : Type] :  El (A ⇝ B) → El A → END → El B;
rule app (abs $M) $N _ ↪ $M $N;

constant symbol Scheme : TYPE;
injective symbol Els : Scheme → TYPE;

constant symbol ↑ : Type → Scheme;
rule Els (↑ $A) ↪ El $A;

constant symbol ∀ₖ : (Type → Scheme) → Scheme;
constant symbol in-∀ₖ [A : Type → Scheme] : (Π x : Type, Els (A x)) → Els (∀ₖ A);
symbol el-∀ₖ [A : Type → Scheme] : Els (∀ₖ A) → Π x : Type, END → Els (A x);
rule el-∀ₖ (in-∀ₖ $A) $x _ ↪ $A $x;

constant symbol prop : Type;
injective symbol Prf : El prop → TYPE;

constant symbol ⇒ : El prop → El prop → El prop;
notation ⇒ infix right 7;
constant symbol in-⇒ [A B : El prop] : (Prf A → Prf B) → Prf (A ⇒ B);
symbol el-⇒ [A B : El prop] :  Prf (A ⇒ B) → Prf A → END → Prf B;
rule el-⇒ (in-⇒ $M) $N _ ↪ $M $N;

constant symbol ∀ [A : Type] : (El A → El prop) → El prop;
constant symbol in-∀ [A : Type] [B : El A → El prop] : (Π x : El A, Prf (B x)) → Prf (∀ B);
symbol el-∀ [A : Type] [B : El A → El prop] : Prf (∀ B) → Π x : El A, END → Prf (B x);
rule el-∀ (in-∀ $P) $x _ ↪ $P $x;

constant symbol ∀ₚ : (Type → El prop) → El prop;
constant symbol in-∀ₚ [A : Type → El prop] : (Π x : Type, Prf (A x)) → Prf (∀ₚ A);
symbol el-∀ₚ [A : Type → El prop] : Prf (∀ₚ A) → Π x : Type, END → Prf (A x);
rule el-∀ₚ (in-∀ₚ $P) $x _ ↪ $P $x;




/*
type : Type.

arrow : type -> type -> type.

bool : type.

def eta : type -> Type.

ptype : Type.

p : type -> ptype.

def etap : ptype -> Type.

forallK : (type -> ptype) -> ptype.

def eps : eta bool -> Type.

impl : eta bool -> eta bool -> eta bool.

forall : t:type -> (eta t -> eta bool) -> eta bool.

forallP : (type -> eta bool) -> eta bool.

[] eta --> t => etap (p t).

[l,r] etap (p (arrow l r)) --> eta l -> eta r.

[f] etap (forallK f) --> x : type -> etap (f x).

[t,f] eps (forall t f) --> x:eta t -> eps (f x).

[l,r] eps (impl l r) --> eps l -> eps r.

[f] eps (forallP f) --> x:type -> eps (f x).
*/
