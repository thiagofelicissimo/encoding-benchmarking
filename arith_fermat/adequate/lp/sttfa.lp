constant symbol Type : TYPE;
injective symbol El : Type → TYPE;

constant symbol ⇝ : Type → Type → Type;
notation ⇝ infix right 7;
constant symbol λ' [A B : Type] : (El A → El B) → El (A ⇝ B);
notation λ' quantifier;
symbol ▪ [A B : Type] :  El (A ⇝ B) → El A → El B;
notation ▪ infix left 7;
rule (λ' $M) ▪ $N ↪ $M $N;

constant symbol Scheme : TYPE;
injective symbol Els : Scheme → TYPE;

constant symbol ↑ : Type → Scheme;
rule Els (↑ $A) ↪ El $A;

constant symbol ∀ₖ : (Type → Scheme) → Scheme;
notation ∀ₖ quantifier;
constant symbol Λ [A : Type → Scheme] : (Π x : Type, Els (A x)) → Els (∀ₖ A);
notation Λ quantifier;
symbol at [A : Type → Scheme] : Els (∀ₖ A) → Π x : Type, Els (A x);
notation at infix left 7;
rule (Λ $A) at $T ↪ $A $T;

constant symbol prop : Type;
injective symbol Prf : El prop → TYPE;

constant symbol ⇒ : El prop → El prop → El prop;
notation ⇒ infix right 7;
constant symbol in-⇒ [A B : El prop] : (Prf A → Prf B) → Prf (A ⇒ B);
symbol el-⇒ [A B : El prop] :  Prf (A ⇒ B) → Prf A → Prf B;
rule el-⇒ (in-⇒ $M) $N ↪ $M $N;

constant symbol ∀ : Π [A : Type], (El A → El prop) → El prop;
notation ∀ quantifier;
constant symbol in-∀ [A : Type] [B : El A → El prop] : (Π x : El A, Prf (B x)) → Prf (∀ B);
symbol el-∀ [A : Type] [B : El A → El prop] : Prf (∀ B) → Π x : El A, Prf (B x);
rule el-∀ (in-∀ $P) $x ↪ $P $x;

constant symbol ∀ₚ : (Type → El prop) → El prop;
notation ∀ₚ quantifier;
constant symbol in-∀ₚ [A : Type → El prop] : (Π x : Type, Prf (A x)) → Prf (∀ₚ A);
symbol el-∀ₚ [A : Type → El prop] : Prf (∀ₚ A) → Π x : Type, Prf (A x);
rule el-∀ₚ (in-∀ₚ $P) $x ↪ $P $x;




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
