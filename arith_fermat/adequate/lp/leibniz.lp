require open coq.sttfa;
symbol leibniz : Els (∀ₖ (λ A, ↑ (A ⇝ A ⇝ prop))) ≔ `Λ A, `λ' x : El (A), `λ' y : El (A), `∀ P : El ((A ⇝ prop)), ((P) ▪ x) ⇒ (P) ▪ y;
symbol refl_leibniz : Prf (`∀ₚ A, `∀ x : El (A), (((leibniz) at (A)) ▪ x) ▪ x) ≔ in-∀ₚ (λ A, in-∀ (λ x : El (A),  in-∀ (λ P : El (A ⇝ prop),  in-⇒ (λ H : Prf ((P) ▪ x), H))));
symbol sym_leibniz : Prf (`∀ₚ A, `∀ x : El (A), `∀ y : El (A), ((((leibniz) at (A)) ▪ x) ▪ y) ⇒ (((leibniz) at (A)) ▪ y) ▪ x) ≔ in-∀ₚ (λ A, in-∀ (λ x : El (A),  in-∀ (λ y : El (A),  in-⇒ (λ p : Prf ((((leibniz) at (A)) ▪ x) ▪ y), in-∀ (λ P : El (A ⇝ prop),  in-⇒ (λ H : Prf ((P) ▪ y), el-⇒ (el-⇒ (el-∀ (p) (`λ' a : El (A), ((P) ▪ a) ⇒ (P) ▪ x)) (in-⇒ (λ px : Prf ((P) ▪ x), px))) (H)))))));
