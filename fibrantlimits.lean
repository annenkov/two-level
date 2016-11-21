import fibrant limit data.equiv algebra.category facts

section pullback

universe variable u
variables {A B C : Type.{max 1 u}}
          (f : A → C) (g : B → C)
          {isfib : is_fibration_alt f}

structure Pullback (f : A → C) (g : B → C):=
  (pA : A)
  (pB : B)
  (pC : C)
  (p_law : (f pA = pC) × (g pB = pC))

definition Pullback' : Type := Σ (b : B), fibreₛ f (g b)

open sigma.ops
definition Pullback'_is_fibrant : is_fibration_alt
  (λ (pb : Pullback' f g), pb.1)
  := λ b, @equiv_is_fibrant _ _ (equiv.symm (fibre_projection b)) (isfib (g b))


-- Inspired by the implementation from HoTT Lean library
inductive pb_cat_ob : Type :=
| obA : pb_cat_ob
| obB : pb_cat_ob
| obC : pb_cat_ob


open pb_cat_ob
inductive pb_cat_hom : pb_cat_ob → pb_cat_ob → Type :=
| f1 : pb_cat_hom obA obC
| f2 : pb_cat_hom obB obC

open sum

definition no_comp_pullback_hom {a b c : pb_cat_ob}
  : pb_cat_hom a b → pb_cat_hom b c → false :=
  begin intros f g, cases g: cases f end


-- Pullback as a category with three objects obA obB and obC
-- and arrows f1 : obA → obC and f2: obB → obC
definition pullback_category : category pb_cat_ob :=
⦃ category,
  hom := λ a b, pb_cat_hom a b + (a = b),
  comp := λ a b c f g,
     begin
       cases f with [f₁, f₂]: cases g with [g₁, g₂],
       { apply inl, exfalso, apply no_comp_pullback_hom g₁ f₁},
       { apply inl, rewrite g₂, assumption},
       { apply inl, rewrite -f₂, assumption},
       { apply inr, rewrite -f₂, assumption}
     end,
  ID := λ a, inr rfl ,
  assoc := λ a b c d h g f,
    begin
    induction h with rh ph: induction g with rg pg: induction f with rf pf:
    try cases pg: try cases pf: esimp: exfalso: apply no_comp_pullback_hom; assumption; assumption
    end,
  id_left := λ a b f, begin cases f with [fl, fr], esimp, cases fr, esimp end,
  id_right := λ a b f, begin cases f with [fl, fr], esimp, cases fr, esimp end ⦄

open category

definition PullbackCat := Mk pullback_category

definition pullback_diagram (f : A → C) (g : B → C) : PullbackCat ⇒ Type_category :=
 ⦃ functor,
   object := λ c,
     match c with
     | obA := A
     | obB := B
     | obC := C
     end,
   morphism := λ a b h,
   begin
    cases h with [pb_hom, p],
    cases pb_hom,
    apply f, apply g, cases p, apply id
   end,
   respect_id := λ a, begin reflexivity end,
   respect_comp :=
     begin
       intros a b c pf pg,
       cases pf with [pb_hom_f, id_f]:
       cases pg with [pb_hom_g, id_g]:
       try (cases pb_hom_f: cases pb_hom_g: esimp):
       try cases id_g: esimp: try cases id_f: esimp
   end ⦄

open functor natural_transformation

definition nat_transf_sigma_iso {C D : Category} {F G : C ⇒ D} :
  F ⟹ G ≃ₛ Σ (η : Π(a : C), hom (F a) (G a)), (Π{a b : C} (f : hom a b), G f ∘ η a = η b ∘ F f) :=
  equiv.mk  (λ N, match N with
                  |mk η NatSq := ⟨η, NatSq⟩
                  end)
            (λ S, match S with
                  | ⟨η, NatSq⟩ := mk η NatSq
                  end)
  begin unfold function.left_inverse, intro x, cases x, esimp end
  begin unfold function.right_inverse, unfold function.left_inverse, intro x, cases x, esimp end

open poly_unit

open equiv

definition const_funct_unit [reducible] [unfold_full] := 
  const_funct_obj PullbackCat Type_category poly_unit.{max 1 u}

definition nat_unit_Pullback_equiv :
  const_funct_unit ⟹ pullback_diagram f g ≃ₛ Pullback f g:=
  begin
    esimp,
    refine (equiv.mk _ _ _ _),
    { intro N, cases N with [η, NatSq], unfold pullback_diagram at *, esimp at *,
      refine Pullback.mk _ _ _ _,
      apply (η obA star), apply (η obB star), apply (η obC star), esimp,
      refine (_,_),
      have H : f ∘ η obA = η obC ∘ id, from NatSq (inl pb_cat_hom.f1), apply happly H,
      have H : g ∘ η obB = η obC ∘ id, from NatSq (inl pb_cat_hom.f2), apply happly H },
    { intro PB, cases PB, cases p_law with [f_eq, g_eq],
      refine mk _ _,
      intros a, unfold pullback_diagram, esimp, intro uu, cases a: esimp: assumption,
      intros a b pb, unfold pullback_diagram, cases pb with [pb_hom, p_id],
      cases pb_hom: esimp,
      { apply funext, intros, apply f_eq},
      { apply funext, intros, apply g_eq},
      { cases p_id, esimp}},
    { unfold function.left_inverse, intros x, cases x,
        esimp at *, congruence, apply funext, intros, apply funext, intro uu, esimp,
        cases x: esimp: cases uu: reflexivity },
    { unfold function.right_inverse, unfold function.left_inverse, intros x,
      cases x, cases p_law with [f_eq, g_eq], esimp }
  end

definition Pullback'_Pullback_equiv : Pullback' f g ≃ₛ Pullback f g:=
  equiv.mk 
    (λ x, begin cases x with [p₁, p₂], cases p₂ with [pp₁, pp₂], 
                apply Pullback.mk pp₁ p₁ (g p₁) (pp₂, rfl) end) 
    (λ x, begin cases x, cases p_law with [p₁, p₂], refine ⟨ pB, #eq.ops ⟨pA, p₁ ⬝ p₂⁻¹⟩⟩end) 
    (λ x, begin cases x with [p₁, p₂], cases p₂ with [pp₁, pp₂], esimp end) 
    (λ x, begin cases x, cases p_law with [p₁, p₂], esimp, cases p₂, esimp end)

open eq

section equiv
  -- TODO: move these definitions to facts.lean or another "library" file
  open eq.ops
  definition sigma_eq_congr {A: Type} {F : A → Type} {a a': A} {b : F a} {b' : F a'} :
    (Σ (p : a = a'), ((p ▹ b) = b')) → ⟨ a, b ⟩ = ⟨a', b'⟩ :=
      begin intro p, cases p with [p₁, p₂], cases p₁, cases p₂, esimp end

  definition sigma_congr₁ [instance] {F : B → Type.{max 1 u}} [φ : A ≃ₛ B]:
  (Σ a : A, F (to_fun B a)) ≃ₛ Σ b : B, F b :=  
  equiv.mk
  (λ x , ⟨ _, x.2 ⟩ )
  (λ x,  ⟨ _, (eq.symm (right_inv A B _)) ▹ x.2⟩ )
  (λ x, begin
        cases x with [x₁, x₂],
        cases φ with [f, g, l, r], unfold function.right_inverse at *, unfold function.left_inverse at *, esimp,
        apply sigma_eq_congr, refine ⟨_,_⟩, apply l,        
        calc
        (l x₁ ▹ ((r (f x₁))⁻¹ ▹ x₂))
            = (r (f x₁))⁻¹ ▹ x₂ : sorry -- apd (λ p, eq.rec x₂ (eq.symm(r (f x₁)))) (l x₁)
        ... = ap f (l x₁)⁻¹ ▹ x₂ : proof_irrel ((r (f x₁))⁻¹) (ap f (l x₁)⁻¹)
        ... = (l x₁)⁻¹ ▹ x₂ : naturality_subst f (l x₁)⁻¹ _
        ... = x₂ : apd _ _
        end)
   begin
     unfold function.right_inverse at *, unfold function.left_inverse at *, intro x, cases x with [p₁, p₂],
     cases φ with [f, g, l, r], esimp,
     esimp, apply sigma_eq_congr, refine ⟨_,_⟩, apply r,
     calc #eq.ops r p₁ ▹ (r p₁)⁻¹ ▹ p₂
         = #eq.ops (r p₁)⁻¹ ▹ p₂ : sorry -- apd (#eq.ops λ p, eq.rec p₂ (r p₁)⁻¹) (r p₁)
     ... = p₂ : sorry   
   end

  definition sigma_congr₂ [instance] {F G : A → Type.{max 1 u}} [φ : Π a : A, F a ≃ₛ G a] :
    (Σ a, F a) ≃ₛ Σ a, G a :=
    equiv.mk sorry sorry sorry sorry

  definition sigma_congr {F : A → Type} {G : B → Type}
    [φ : A ≃ₛ B] [φ' : Π a : A, F a ≃ₛ G (to_fun B a)] :
    (Σ a, F a) ≃ₛ Σ a, G a := equiv.trans sigma_congr₂ sigma_congr₁
  
end equiv

open equiv

definition nat_unit_equiv_sigma {C : Category} {X : C ⇒ Type_category } :
  (const_funct_obj C Type_category unit ⟹ X) ≃ₛ Σ (c : Π y : C, X y), Π (y y' : C) (f : y ⟶ y'), (X f) (c y) = c y' :=
  begin
  apply equiv.trans (nat_transf_sigma_iso),
  -- this equivalence helps automatically resolve some goals 
  -- using type class instances mechanism
  assert Hequiv : (Π a, object (const_funct_obj C Type_category unit) a⟶ X a) ≃ Π y, X y,
  begin esimp, refine equiv.mk (λ a y, a y unit.star) (λ a y x, a y) _ (λx, rfl), 
    unfold function.left_inverse, intros, apply funext, intros, apply funext, intros, cases x_2, reflexivity,
  end,
  apply @sigma_congr,
  
  intros f,  
  apply @pi_congr₂, intro a, apply @pi_congr₂, intro b, apply @pi_congr₂, intro f',  
  esimp at *, rewrite id_right,
  refine equiv.mk _ _ _ _,
  have  Hequiv' : (unit → X b) ≃ X b, from unit_arrow_equiv _,
  intro p, cases Hequiv with [ff,gg,l,r], unfold function.right_inverse at *, unfold function.left_inverse at *, esimp at *,
  
  end


end pullback
