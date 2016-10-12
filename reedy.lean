import fibrant data.fin data.equiv

open nat equiv function fin

definition pi_is_fibrant'' {X : Type}{Y : X → Type}
(fibX : is_fibrant X) (fibY : Π (x : X), is_fibrant (Y x)) :
is_fibrant (Π (x : X), Y x) :=
is_fibrant.mk (pi_is_fibrant' fibX fibY)

open sum equiv.ops

definition fam_indexed_by_empty_equiv_unit {X : empty → Type}: (Π i, X i) ≃ unit :=
  equiv.mk (λ x, unit.star) (λ x, empty.rec X) 
           begin unfold left_inverse, intro, apply funext, intro, cases x_1  end
           begin 
             intro, cases x, reflexivity  
           end

definition fin_0_fam_equiv.{u} : (fin 0 → Type.{u}) ≃ (empty → Type.{u}) :=
  begin apply arrow_congr, apply fin_zero_equiv_empty, apply equiv.refl end

definition pi_fin0_unit_equiv {X : fin 0 → Type} : (Π i, X i) ≃ unit :=
  equiv.mk (λ x, unit.star) (λ x i, fin.elim0 i)
  begin unfold left_inverse, intro, apply funext, intro, apply (elim0 x_1) end
  begin 
  intro, cases x, reflexivity
  end

open unit prod.ops
  
lemma pi_sum_fin_unit_equiv {n} {X : (unit + fin n) → Type} : (Π i, X i) ≃ (X (inl ⋆) × Π i, X (inr i)) :=
  equiv.mk (λ x, (x (inl ⋆), λ y, x (inr y))) (λ p, λ z, sum.cases_on z (λ x1, unit.cases_on x1 p.1) (λ x2, p.2 x2)) 
  begin 
    unfold left_inverse, esimp, intro, apply funext, intro, 
    cases x_1, 
      esimp, cases a, esimp, 
      esimp
  end
  begin
    unfold right_inverse, unfold left_inverse, apply prod.eta
  end

definition pi_sum_fin_unit_equiv' {n} {Heq : fin n + unit ≃ fin (nat.succ n)}
      {X : fin (nat.succ n) → Type} 
      : (Π i, X (Heq ∙ i)) ≃ (X (Heq ∙ (inr ⋆)) × Π i, X (Heq ∙ (inl i))) :=
 equiv.mk 
   (λ x, (x (inr ⋆), λ y, x (inl y))) 
   (λ p, λ z, sum.cases_on z (λ x2, p.2 x2) (λ x1, unit.cases_on x1 p.1)) 
   begin 
     unfold left_inverse, esimp, intro, apply funext, intro, 
     cases x_1, esimp, cases a, esimp
   end
   begin
     unfold right_inverse, unfold left_inverse, apply prod.eta
   end


lemma equiv_id_left {A B : Type} [eq : A ≃ B] {i : A} : (@equiv.inv _ _ eq (equiv.fn eq i)) = i :=
  begin apply equiv.left_inv end

lemma equiv_id_right {A B : Type} [eq : A ≃ B] {i : B} : (equiv.fn eq (@equiv.inv _ _ eq i)) = i :=
begin apply equiv.right_inv end

set_option formatter.hide_full_terms false

lemma pi_congruence {A B : Type} [HequivAB : A ≃ B] {X : A → Type}
                    : (Π (i : A), X i) ≃ (Π (i : B), X (equiv.inv i)) := 
      equiv.mk (λ x y, x _) 
               (begin 
                 intros, 
                 have H : X (inv (equiv.fn HequivAB i)), from (a (equiv.fn HequivAB i)), 
                 have H1 : X i, from eq.rec_on (@equiv_id_left A B HequivAB i) H,
                 exact H1
                 end) sorry sorry
               --(begin unfold left_inverse, intros, apply funext, intros, apply equiv_id, end) 
               --(begin unfold right_inverse, unfold left_inverse, intros, apply funext, intros, apply equiv_id end)

definition pi_congruence' {A B : Type} [equiv : A ≃ B] {X : B → Type} : 
                     (Π (i : A), X (equiv.fn _ i)) ≃ (Π (i : B), X i) := 
      equiv.mk (begin intros Hpi i,
                have H : X i, from eq.rec_on (@equiv_id_right A B equiv i) (Hpi (equiv.inv i)),
                exact H
                end)
      (λ x i, x (equiv.fn _ i))
      sorry sorry
--(begin unfold left_inverse, intros, apply funext, intros, apply equiv_id, end) 
--(begin unfold right_inverse, unfold left_inverse, intros, apply funext, intros, apply equiv_id end)

definition prod_is_fibrant'' [instance] {X Y : Type} 
{fibX : is_fibrant X} {fibY : is_fibrant Y} :
is_fibrant (X × Y) := is_fibrant.mk (prod_is_fibrant' fibX fibY)

definition lemma3 {n : ℕ}
                  {X : fin n → Type}
                  {fibX : Π i, is_fibrant (X i)}
  : is_fibrant (Π i, X i) := 
begin
  induction n,  
  apply equiv_is_fibrant, apply (equiv.symm pi_fin0_unit_equiv),
  
  have HeqFinSum : fin (succ a) ≃ fin a + unit, from (equiv.symm (fin_sum_unit_equiv a)),
  apply equiv_is_fibrant, apply (@pi_congruence' _ _ HeqFinSum⁻¹ _),  apply equiv_is_fibrant, apply equiv.symm,
  apply (@pi_sum_fin_unit_equiv' a (equiv.symm HeqFinSum) X), apply (@prod_is_fibrant'' _ _), apply fibX, apply v_0,
  intro, apply fibX
end
