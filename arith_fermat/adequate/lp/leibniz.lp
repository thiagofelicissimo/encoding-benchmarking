require open coq.sttfa;
symbol leibniz : Els (∀ₖ (λ A, ↑ (A ⇝ A ⇝ prop))) ≔ in-∀ₖ (λ A, abs (λ x : El (A), abs (λ y : El (A), ∀ (λ P : El ((A ⇝ prop)), (app (P) x ■) ⇒ app (P) y ■))));
symbol refl_leibniz : Prf (∀ₚ (λ A, ∀ (λ x : El (A), app (app (el-∀ₖ (leibniz) (A) ■) x ■) x ■))) ≔ in-∀ₚ (λ A, in-∀ (λ x : El (A),  in-∀ (λ P : El (A ⇝ prop),  in-⇒ (λ H : Prf (app (P) x ■), H))));
constant symbol sym_leibniz : Prf (∀ₚ (λ A, ∀ (λ x : El (A), ∀ (λ y : El (A), (app (app (el-∀ₖ (leibniz) (A) ■) x ■) y ■) ⇒ app (app (el-∀ₖ (leibniz) (A) ■) y ■) x ■))));
