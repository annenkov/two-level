import fibrant matching inverse algebra.category 
       limit pullbacks data.fin finite        

open invcat category functor matching_object Fib 
     sigma.ops fincat natural_transformation eq

structure subcat_obj (C : Category) (p : objects C → Prop) :=
  (obj : objects C)
  (prop : p obj)

open subcat_obj function
attribute subcat_obj.obj [coercion]

definition subcat [instance] (C : Category) (p : C → Prop) : category (subcat_obj C p) :=
  ⦃ category,
    hom := λ (a b : subcat_obj C p), obj a ⟶ obj b,
    comp := λ a b c, @comp _ _ _ _ _,
    ID := λ (a : subcat_obj C p), ID (obj a),
    assoc := λ a b c d h g f, assoc h g f,
    id_left := λ a b f, id_left f,
    id_right := λ a b f, id_right f ⦄

definition Subcat (C : Category) (p : C → Prop) : Category := Mk (subcat C p)

open equiv equiv.ops

namespace reedy
  universe variable u
  variables {C : Category.{1 1}} [invcat C]

  definition is_reedy_fibrant [class] (X : C ⇒ Type_category) :=
    Π z, is_fibration_alt (matching_obj_map X z)
end reedy

namespace fiblimits
  universe variable u
  variables {C : Category.{1 1}}
            {D : Category}

  open nat fin subcat_obj reedy
  
  -- we also refer to this category as C'
  definition C_without_z (z : C) : Category := Mk (subcat C (λ c, c ≠ z))

  -- (Danil) I have to use apply tactic, as it allows to infer correct implicits
  definition Functor_from_C' [reducible] (z : C) (X : C ⇒ D) : C_without_z z ⇒ D :=
  ⦃ functor,
    object := λ ob, X (obj ob),
    morphism := λ a b f, by apply X f,
    respect_id := λ a, by apply respect_id X (obj a),
    respect_comp := λ a b c g f, by apply @respect_comp _ _ X (obj a) (obj b) (obj c) _ _
  ⦄

  open eq.ops function
  definition C_without_z_invcat [instance] (z : C) [invC : invcat C] : invcat (C_without_z z) :=
    begin
      unfold C_without_z, cases invC, cases reflecting_id_ℕop,
      refine invcat.mk (has_idreflect.mk _ _), apply Functor_from_C' z φ, intros x y f p,
      cases reflecting_id f p with [p1, p2],
      refine ⟨_,_⟩,
      { cases x, cases y, congruence, apply p1 },
      { cases x, cases y, esimp at *, induction p1 using eq.drec, esimp at *, apply p2}
    end

  definition C_without_z_sigma_equiv {C : Category} (z : C) : C_without_z z ≃ₛ Σ (c : C), c ≠ z :=
  equiv.mk (λ c', ⟨obj c', prop c'⟩) (λc, mk c.1 c.2) begin intros, cases x, esimp, end begin intros, cases x, esimp end

  definition C_without_z_is_finite [instance] {n : ℕ} (z : C) [φ : objects C ≃ₛ fin (nat.succ n)]
  : objects (C_without_z z) ≃ₛ fin n :=  (fincat_ob_remove_fin_equiv z) ∘ (C_without_z_sigma_equiv z)
    
  open sum
  
  definition has_lt_ℕop [instance] : has_lt ℕop := nat_has_lt
  definition strict_order_ℕop [instance] : strict_order ℕop := 
    strict_order.mk nat.lt (@lt.irrefl ℕ _) (λ a b c, @nat.lt_trans a b c)
  definition weak_order_ℕop [instance] : weak_order ℕop := 
    weak_order.mk nat.le (@le.refl ℕ _) (λ a b c, @nat.le_trans a b c) (λ a b, nat.le_antisymm)


  definition max_fun_to_ℕ (φ : C → ℕ) {n : ℕ} [ψ : objects C ≃ₛ fin (nat.succ n)] :
  Σ z, (Π c, φ c ≤ φ z) :=
  begin
    generalize φ, clear φ, generalize ψ, clear ψ, generalize C, clear C,
    induction n with [n', IHn],
    intros,    
    { cases ψ with [f,g,l,r], esimp at *,
      existsi g (fin.zero 0),       
      intro, assert H : f c = zero, apply eq_of_veq, cases (f c) with [v, Hlt], esimp, cases v, 
      reflexivity, cases Hlt with [a, Hle], exfalso, 
      rewrite -(succ_le_zero_iff_false (succ a)), apply Hle, rewrite -l, rewrite H },
    { intros,
      have H : Σ z, @to_fun _ (fin (succ (nat.succ n'))) ψ z = maxi, from ⟨(inv_fun C maxi), !right_inv⟩,
      cases H with [z'', max_z],
      have ψ' : C_without_z z'' ≃ fin (succ n'), from (@C_without_z_is_finite _ _ z'' _),
      have H : Π (φ : C_without_z z'' → ℕ), 
               Σ (z : C_without_z z''), (Π c, φ c ≤ φ z),
      from IHn _ ψ',
      cases H (φ ∘ obj) with [z', Hmax],
      cases (@decidable_le (φ z'') (φ z')) with [z_le, z_ne_le],
      existsi z', intros,
      cases (@fincat.has_decidable_eq _ ⟨succ (succ n'), ψ⟩ c z'') with [c_eq_z, c_ne_z],
      { rewrite c_eq_z, assumption },
      { apply Hmax (mk _ c_ne_z) },
        existsi z'', intro, apply nat.le_of_eq_or_lt,
        cases (@fincat.has_decidable_eq _ ⟨succ (succ n'), ψ⟩ c z'') with [c_eq_z, c_ne_z],
        left, rewrite c_eq_z, right, 
        have Hmax_c' : φ (obj (mk c c_ne_z)) ≤ φ (obj z'), from Hmax (mk c c_ne_z), esimp at *,
        have Hlt : φ z' < φ z'', from iff.elim_right (gt_iff_not_le _ _) z_ne_le,
        apply lt_of_le_of_lt Hmax_c' Hlt }
  end
  
  open invcat

definition no_incoming_non_id_arrows (z : C) {φ : C ⇒ ℕop} {max_rank : ∀ y, φ y ≤ φ z} 
    {reflecting_id : id_reflect φ}
    : ¬ ∃ y : C, ∃ (f : y ⟶ z), y ≠ z :=
    begin intro H, cases H with [y, s], cases s with [f, y_ne_z], unfold id_reflect at *,
    have H : φ y ≥ φ z, from φ f,
    cases reflecting_id f ⟨le.antisymm (max_rank y) H, rfl⟩ with [p, Heq],
    apply y_ne_z, assumption
    end

  definition Functor_from_C'_eq (X : C ⇒ Type_category) (z : C) (x' : C_without_z z) :
    X (@obj _ _ x') = (object (Functor_from_C' z X) x') := 
    begin esimp end
  
    open poly_unit
    open reduced_coslice
    open reduced_coslice.red_coslice_obs

    -- for any object "a" from z//C (which is an arrow z⟶y with extra property) we show that codomain y cannot be z
    -- we show it using the definition of reduced coslice and the fact that C is an inverse category
    definition reduced_coslice_ne (z : C) (a : z//C) [invC : invcat C] : to a ≠ z :=
    begin
      cases a with [y, f, non_id_f], esimp at *,
      intro p, cases p,
      apply non_id_f rfl,
      cases invC, cases reflecting_id_ℕop,
      apply (reflecting_id f ⟨rfl,rfl⟩).2
    end
  
  section MO_facts
    -- constructions related to properties of a matching object after
    -- we remove maximal element from the finite inverse category C

    open reduced_coslice reduced_coslice.coslice_obs
    
    variables {z : C} {x : C_without_z z}
              {φ : C ⇒ ℕop} {reflecting_id : id_reflect φ}
              {max_rank : ∀ x, φ x ≤ φ z}
              [is_finite C] [invcat C]
              (X : C ⇒ Type_category)

    definition red_coslice_to_C' (o : x//C_without_z z) : (obj x)//C :=
    begin 
      cases o with [t,f,non_id],
      refine red_coslice_obs.mk (obj t) f _, intros p, intros q,
      assert H : @eq (C_without_z z) x t, begin cases x, cases t, esimp at *, congruence, assumption end,      
      apply non_id H, cases H, esimp, apply q
    end    

    definition red_coslice_to_C'_hom (a b : x//C_without_z z) (f : a ⟶ b) : (red_coslice_to_C' a) ⟶ (red_coslice_to_C' b) := 
    begin 
      cases f with [f, comm_tr], cases a with [a,g,non_id], cases b with [b,g', non_id'], 
      unfold red_coslice_obs.to_coslice_obs at *, unfold red_coslice_to_C' at *, esimp at *,
      apply ⟨f,comm_tr⟩
    end

    -- (Danil) I pack this property as a lemma to prevent unnessesary unfolding
    -- which sometimes leads to errors when unfolding definitions dependent on this one
    lemma subcat_obj_eq {c c1: C} {P : C → Prop} {p : P c} {p1 : P c1} 
      (q : subcat_obj.mk c p = subcat_obj.mk c1 p1) : c = c1 :=
      begin refine subcat_obj.no_confusion q (λ x y, x) end

    include φ max_rank reflecting_id

    definition red_coslice_ne_z (t : C) (f : x ⟶ t) : t ≠ z :=
    begin
      cases x with [x', x'_ne], esimp at *,
      cases (@fincat.has_decidable_eq _ _ t z) with [t_eq_z, t_ne_z], cases t_eq_z, exfalso,
      apply @no_incoming_non_id_arrows _ z φ max_rank reflecting_id, existsi x', existsi f, apply x'_ne, apply t_ne_z
    end    
    
    definition red_coslice_from_C' [reducible] (o : (obj x)//C) : x//C_without_z z :=
    begin
      cases o with [t,f,non_id], esimp at *, 
      cases x with [x', x'_ne], esimp at *,      
      let t' := subcat_obj.mk t
      (@red_coslice_ne_z _ z (mk x' x'_ne) φ reflecting_id max_rank _ _ t f),
      refine red_coslice_obs.mk _ _ _, apply t', apply f, intros p,
      intros q,
      have q1 : x' = t, from subcat_obj_eq p,
      apply non_id q1, cases q1, esimp at *, apply q
    end    

    definition red_coslice_from_C'_hom {a b : x//C} (f : a ⟶ b) :
    (@red_coslice_from_C' _ _ _ _ reflecting_id max_rank _ _ a) ⟶ (@red_coslice_from_C' _ _ _ _ reflecting_id max_rank _ _ b) := 
    begin
      cases f with [f, comm_tr], cases a with [a,g,non_id], cases b with [b,g', non_id'],
      unfold red_coslice_obs.to_coslice_obs at *, unfold red_coslice_from_C' at *, esimp at *,
      cases x, esimp at *,
      apply ⟨f,comm_tr⟩,
    end

    definition red_coslice_without_z_equiv : (obj x)//C ≃ₛ (x//C_without_z z) :=
    equiv.mk (@red_coslice_from_C' C _ _ _ reflecting_id max_rank _ _) red_coslice_to_C'
    begin
      intros y, cases y with [y,f,non_id],
      cases x with [x, x_ne], esimp  
    end 
    begin
      intros y, cases y with [y,f,non_id], unfold red_coslice_to_C', 
      cases y, esimp, unfold red_coslice_from_C', cases x, esimp
    end

    definition red_coslice_eq_1 :
    ∀ y, object X (obj (red_coslice_obs.to ((@red_coslice_without_z_equiv  _ _ x _ reflecting_id max_rank _ _) ∙ y))) = 
      X (red_coslice_obs.to y) := 
      begin
        intro, unfold fn, cases y with [y,f,y_ne], cases x with [x, x_ne], esimp
      end
  
    definition MO'_to_MO_map : 
    matching_object (Functor_from_C' z X) x → matching_object X (obj x) :=
    begin
      let ψ := @red_coslice_without_z_equiv C z _ φ reflecting_id max_rank _ _,
      intros a,
      refine natural_transformation.mk _ _,
      { intros y uu, unfold functor.compose at *, unfold forget at *, esimp at *, unfold red_coslice_obs.to_coslice_obs, 
        unfold Functor_from_C' at *, 
        have HH : object X (red_coslice_obs.to (ψ ∙ y)), from (natural_map a) (ψ ∙ y) star,
        intro, unfold fn at *,
        cases y with [y,f,y_ne], cases x with [x', x_ne], esimp at *, 
        apply HH },
      { cases a with [η, NatSq], intros x' y,        
        intros f',
        let X' := Functor_from_C' z X,
        let C' := C_without_z z,
        assert HH : #function
        morphism (X' ∘f forget C' x) (red_coslice_from_C'_hom f') ∘ η (red_coslice_from_C' x') = 
        η (@red_coslice_from_C' _ _ _ _ reflecting_id max_rank _ _ y),
        begin apply NatSq _ end,
        cases x with [x,f,non_id_f], cases y with [y,g,non_id_g], esimp at *,        
        cases f' with [a,p1], esimp,
        cases x' with [o, o_ne], esimp,
        unfold Functor_from_C' at *, unfold functor.compose at *, unfold forget at *, esimp at *,
        unfold red_coslice_from_C'_hom at *, esimp at *,
        rewrite natural_map_proj,
        apply funext, intros uu, esimp, esimp, cases uu, refine happly HH _ }
    end

    definition MO_equiv : matching_object (Functor_from_C' z X) x ≃ₛ matching_object X (obj x) :=
    begin
      let C' := C_without_z z,
      let X' := Functor_from_C' z X,
      let  ψ := @red_coslice_without_z_equiv C z x φ reflecting_id max_rank _ _,
      
      -- we got two commuting triangles using equivalence  ((obj x)//C) ≃ (x//C')
      assert Htr1 : ∀ y, (X' ∘f !forget) (@to_fun _ _ ψ y) = (X ∘f !forget) y,
        begin intro, unfold functor.compose, unfold forget, unfold Functor_from_C',
          unfold red_coslice_obs.to_coslice_obs, esimp, refine red_coslice_eq_1 _ _,
        end,      
      assert Htr2 : ∀ y, (X ∘f !forget) (@inv_fun _ _ ψ y) = (X' ∘f (!forget)) y, 
        begin intro, unfold functor.compose, unfold forget, unfold Functor_from_C',
      unfold red_coslice_obs.to_coslice_obs, cases y with [y,f,y_ne], esimp end,
      unfold matching_object,
      refine equiv.mk (@MO'_to_MO_map _ _ _ _ reflecting_id max_rank _ _ X) _ _ _,      
      { intros a, cases a with [η, NatSq], refine natural_transformation.mk _ _,
        intros y uu, 
        have η' :  poly_unit → (X∘f forget C (obj x)) (@equiv.inv _ _ ψ y), from η _,
        intro, unfold functor.compose at *, unfold forget at *, unfold Functor_from_C' at *,
        unfold red_coslice_obs.to_coslice_obs, cases y with [y,f,y_ne], esimp, apply η' star,
        intros a b f,
        assert HH : morphism (X∘f forget C (obj x)) (red_coslice_to_C'_hom _ _ f) ∘ η (red_coslice_to_C' a) 
        = η (red_coslice_to_C' b), 
        begin refine NatSq _ end,
        unfold Functor_from_C' at *, unfold functor.compose at *, unfold forget at *, esimp at *,
        unfold red_coslice_to_C'_hom at *, esimp at *,
        cases f with [f,comm_tr], cases a with [a, ff, non_id_ff ], cases b with [b, gg, non_id_gg],
        apply funext, intros uu, cases uu,
        refine happly HH _},
      { intros a, refine nat_trans_eq, cases a with [η, NatSq], rewrite natural_map_proj,
        unfold MO'_to_MO_map, unfold fn, unfold equiv.inv, rewrite natural_map_proj,
        apply funext, intro y, apply funext, intro uu, cases uu,
        have Heq : (@to_fun _ _ ψ (@inv_fun (obj x//C) _ ψ y)) = y, from by apply right_inv,
        cases Heq, cases y with [y,f,non_id_f], esimp at *, cases x with [x,p], esimp },
      { intros a, refine nat_trans_eq, cases a with [η, NatSq],
        esimp, rewrite natural_map_proj,
        unfold MO'_to_MO_map, rewrite natural_map_proj,
        apply funext, intro y, apply funext, intro uu, cases uu,
        cases y, cases x, esimp }
    end

  end MO_facts
  
  
  definition Functor_from_C'_reedy_fibrant (z : C) (X : C ⇒ Type_category) [invC : invcat C]
    {φ : C ⇒ ℕop} {max_rank : ∀ x, φ x ≤ φ z} {reflecting_id : id_reflect φ}
    [rfibX : is_reedy_fibrant X] [finC : is_finite C]
    : is_reedy_fibrant (Functor_from_C' z X)  :=
      begin
        let C' := C_without_z z,
        let X' := Functor_from_C' z X,
        unfold is_reedy_fibrant at *,
        unfold is_fibration_alt at *,
        intros x b,
        let Hequiv := (@MO_equiv C z x φ reflecting_id max_rank _ _ X),
        let MO := @to_fun _ _ Hequiv b,
        assert isfibX' : is_fibrant (fibreₛ (matching_obj_map X (obj x)) (@to_fun _ _ Hequiv b)), begin apply (rfibX x MO) end,
        assert Hfeq': (fibreₛ (matching_obj_map X (obj x)) MO) ≃ₛ (fibreₛ (matching_obj_map (Functor_from_C' z X) x) b),
        begin
          unfold fibreₛ, apply @sigma_congr₂, intros, esimp,
          apply iff_impl_equiv, refine iff.intro _ _,
          { intros p,
            calc
                  matching_obj_map X' x a
                = @inv_fun _ _ Hequiv (matching_obj_map X (obj x) a) : 
                    begin refine nat_trans_eq, apply funext, intro y, apply funext, intro uu, 
                        cases y, cases uu, esimp end
            ... = @inv_fun _ _ Hequiv (@to_fun _ _ Hequiv b) : ap _ p
            ... = b : @left_inv _ _ _
            },
          { intros p,
            calc
                 matching_obj_map X (obj x) a
                 = Hequiv ∙ (matching_obj_map X' x a) : 
                 begin 
                   unfold fn, refine nat_trans_eq, apply funext, intro y, apply funext, intro uu, 
                  cases uu, esimp at *,
                  assert H : morphism X (hom_to y) a =
                  natural_map ((@MO'_to_MO_map _ _ _ _ reflecting_id max_rank _ _ X) 
                  (matching_obj_map (Functor_from_C' z X) x a)) y star, unfold MO'_to_MO_map, 
                  rewrite natural_map_proj, cases y, esimp, cases x, esimp,
                  apply H end
           ... = Hequiv ∙ b : ap _ p }
        end,
        apply equiv_is_fibrant Hfeq'
      end  

  -- map from limit of X restricted to C'
  definition map_L_to_Mz (z : C) (X : C ⇒ Type_category) [invC : invcat C]
    (L : cone_with_tip (Functor_from_C' z X) poly_unit) : matching_object X z :=
      by cases L with [η, NatSq]; refine natural_transformation.mk
        (λ a u, η (mk (to a) (reduced_coslice_ne z a)) poly_unit.star)
        (λ a b f, begin apply funext, intro, cases x, refine happly (NatSq _) poly_unit.star end)


  -- explicit representation of the limit of X restricted to category C without z
  definition lim_restricted [reducible] (X : C ⇒ Type_category) (z : C) [invC : invcat C]
  := Σ (c : Π y, (Functor_from_C' z X) y),
        Π (y y' : C_without_z z) (f : @hom (subcat_obj C _) _ y y'),
          ((Functor_from_C' z X) f) (c y) = c y'

  -- map from limit of X restricted to C' where we use explicit representation of limit L
  definition map_L_to_Mz_alt (z : C) (X : C ⇒ Type_category.{u}) [invC : invcat C]
  (L : lim_restricted X z) : matching_object X z :=
    match L with
    | ⟨η, NatSq⟩ :=
    by refine natural_transformation.mk
    (λ a u, η (mk _ (reduced_coslice_ne z a)))
    (λ a b f, funext (λ u, NatSq _ _ _))
  end

  definition lift_to_rc [reducible] {z : C} (y : C_without_z z) (f : z ⟶ obj y): z//C :=
    red_coslice_obs.mk (obj y) f (λ p a, prop y p⁻¹)

  definition singleton_contr_fiberₛ {E B : Type} {p : E → B} : (Σ b, fibreₛ p b) ≃ₛ E :=
  begin
    refine equiv.mk (λ (p' : (Σ b, fibreₛ p b)), p'.2.1) (λ e, ⟨p e, ⟨e,rfl⟩⟩) _ (λx, rfl),
    unfold function.left_inverse, intros, cases x with [p1, p2], cases p2 with [p21,p22],
    esimp, induction p22 using eq.drec, congruence
  end  

  definition two_piece_limit_pullback_p_q_equiv [invC : invcat C] (X : C ⇒ Type_category.{u}) (z : C) :
  (Σ (c_z : X z) (c : (Π y : C_without_z z, X y)),
  (Π (y : C_without_z z) (f : z ⟶ obj y ), X f c_z = c y) ×
  (Π (y y' : C_without_z z) (f : @hom (subcat_obj _ _) _ y y'), (Functor_from_C' z X) f (c y) = c y'))
    ≃ₛ
  (Σ (c_z : X z) d, !map_L_to_Mz_alt d = !matching_obj_map c_z)
   :=
  begin
    refine @sigma_congr₂ _ _ _ _, intro c_z,
    refine equiv.mk _ _ _ _,
    { intro w, refine ⟨_,_⟩, refine ⟨w.1, prod.pr2 w.2⟩,
      unfold map_L_to_Mz_alt, refine nat_trans_eq, unfold natural_map,
      apply funext, intro y, apply funext, intro u, unfold matching_obj_map,
      esimp, cases w with [c,p2], cases p2 with [p_l, p_r], esimp at *, symmetry,
      apply (p_l (subcat_obj.mk (to y) (reduced_coslice_ne z y)) (hom_to y)) },
    { intro w,
      cases w  with [d, Heq], unfold lim_restricted at d, cases d with [c, Heq'], existsi c,
      split,
      { intros,
        assert H: natural_map (!map_L_to_Mz_alt ⟨c, Heq'⟩) (lift_to_rc y f) star  =
                  natural_map (!matching_obj_map c_z) (lift_to_rc y f) star, begin rewrite Heq end,
        assert lemma1 : natural_map (map_L_to_Mz_alt z X ⟨c,Heq'⟩) (lift_to_rc y f) star = c y,
          begin unfold map_L_to_Mz_alt, unfold natural_map, cases y, esimp end,
        have lemma2 : (natural_map (matching_obj_map X z c_z)) (lift_to_rc y f) star = X f c_z, from rfl,
        symmetry,
        apply #eq.ops lemma1⁻¹ ⬝ H ⬝ lemma2 },
      { apply Heq'}},
    { intro w, cases w with [c, H], cases H with [p1,p2], apply sigma_eq_congr, existsi rfl, apply apd },
    { intro w, cases w with [c, H], apply sigma_eq_congr, refine ⟨_,_⟩, cases c with [p1,p2],
    apply sigma_eq_congr, existsi rfl, refine apd _ _, apply p2, reflexivity, apply proof_irrel  }
  end

  definition lim_two_pieces_eq
  {X : C ⇒ Type_category.{u}}
  { z : C }
  { c_z : X z}
  { c : Π y, X (obj y) }
  {a b : (Π (y : C_without_z z) (f : z ⟶ obj y ), X f c_z = c y) ×
  (Π (y y' : C_without_z z) (f : @hom (subcat_obj _ _) _ y y'), (Functor_from_C' z X) f (c y) = c y')} : a = b :=
  begin cases a, cases b, congruence end

  definition limit_two_piece_limit_equiv [invC : invcat C] {n' : ℕ} 
    (ψ : C ≃ₛ fin (succ n'))
    {z : C}
    {φ : C ⇒ ℕop}
    (reflecting_id : id_reflect φ)
    (max_rank : Πy, φ y ≤ φ z)
    (X : C ⇒ Type_category.{u}) :
    (Σ (c : Π y, X y), Π y y' f, morphism X f (c y) = c y')
      ≃ₛ
    (Σ (c_z : X z) (c : (Π y : C_without_z z, X y)),
    (Π (y : C_without_z z) (f : z ⟶ obj y ), X f c_z = c y) ×
    (Π (y y' : C_without_z z) (f : @hom (subcat_obj _ _) _ y y'), (Functor_from_C' z X) f (c y) = c y'))
    := begin
       refine equiv.mk _ _ _ _,
                { intro, cases a with [p1, p2], refine ⟨p1 z, ⟨λ y, p1 y,(λ y' f, p2 z y' f, λ y y' f, p2 y y' f)⟩⟩ },
                { intro, cases a with [c_z, p'], cases p' with [p2, p3], cases p3 with [l_z, l_y], refine ⟨_,λ y y' f, _⟩, intro y'',
                  have Heq : decidable (y'' = z), from @fincat.has_decidable_eq _ (⟨_,ψ⟩) _ _,
                  cases Heq with [y_eq_z, y_ne_z],
                  { rewrite y_eq_z, assumption },
                  { refine p2 (mk y'' _), assumption },
                  intros,
                  -- now, we have 4 cases to consider: y=z, y≠z, y'=z, y'≠z
                  generalize (@fincat.has_decidable_eq C ⟨_,ψ⟩ y  z),
                  generalize (@fincat.has_decidable_eq C ⟨_,ψ⟩ y' z),
                  intros deq_y deq_y',
                  cases deq_y' with [y_eq_z, y_ne_z]:
                  cases deq_y with [y'_eq_z, y'_ne_z],
                  { cases y_eq_z, cases y'_eq_z, esimp, rewrite (endomorphism_is_id f), refine happly (respect_id _ _) _},
                  { cases y_eq_z, esimp, apply l_z},
                  { cases y'_eq_z, esimp, exfalso, apply (@no_incoming_non_id_arrows _ z φ max_rank _), existsi y, existsi f, assumption },
                  { esimp, apply l_y },
                },

                { unfold left_inverse, esimp, intros, cases x with [x, H], esimp, congruence, apply funext, intro y,
                  cases @fincat.has_decidable_eq C (⟨_,ψ⟩) y  z with [y_eq_z, y_ne_z],
                { cases y_eq_z, esimp }, {esimp }},

                { unfold right_inverse, unfold left_inverse, esimp, intro y, cases y with [c_z, Hs],
                  esimp, cases Hs with [p1, p2], esimp, cases p2, esimp,
                  cases (@has_decidable_eq C ⟨succ n', ψ⟩ z z) with [y_eq_z, y_ne_z], esimp, congruence,
                  apply sigma_eq_congr,
                  refine ⟨_,lim_two_pieces_eq⟩,
                  { intros, apply reflecting_id, assumption },
                  { apply funext, intro y',
                    cases @fincat.has_decidable_eq C (⟨_,ψ⟩) y' z with [y'_eq_z, y'_ne_z], esimp,
                    cases y' with [y'', p'], esimp at *, exfalso, apply p', apply y'_eq_z,
                    esimp, cases y', congruence },
                  exfalso, apply y_ne_z, reflexivity
              }
           end

  definition fibration_domain_is_fibrant {E : Type} {B : Fib} (p : E → B) [isfibr_p : is_fibration_alt p]:
    is_fibrant E := @equiv_is_fibrant (Σ b x, p x = b) _ singleton_contr_fiberₛ _

  definition fincat_0_limit_unit_equiv [φ : C ≃ₛ fin 0 ] (X : C ⇒ Type_category) : Nat(𝟙,X) ≃ₛ poly_unit :=
    begin
    cases φ with [f,g,l,r],
    refine equiv.mk (λ x, star) _ _ _,
    { intros, esimp, refine mk _ _, intros x, exfalso, apply (false_of_fin_zero (f x)),
      intros a b u, exfalso, apply (false_of_fin_zero (f a))},
    { unfold left_inverse, intro L, cases L, congruence, apply funext, intro x, exfalso, apply (false_of_fin_zero (f x))},
    { unfold right_inverse, unfold left_inverse, intro x, cases x, reflexivity }
    end

  definition fibrant_limit.{v} [invC : invcat C] [finC : is_finite C]
    (X : C ⇒ Type_category) (rfib : is_reedy_fibrant X) :
    is_fibrant (limit_obj (limit_in_pretype X)) :=
    begin
      cases finC with [n, ψ],
      revert ψ, revert rfib, revert invC, revert X, revert C,
      induction n with [n', IHn],
      { intros C X invC rfib ψ, apply equiv_is_fibrant.{v} (@fincat_0_limit_unit_equiv _ ψ X)⁻¹ },
      { intros C X invC rfib ψ, esimp,        
        have inv_C : invcat C, from invC,        
        cases invC, cases reflecting_id_ℕop with [φ, idrefl],
        -- choosing an element of C with maximal rank
        have H : Σ z, (Π (y : C), φ y ≤ φ z), from @max_fun_to_ℕ _ φ _ ψ,
        cases H with [z, z_max_φ],
        -- removing z from C and showing that the resulting category
        -- is still inverse and finite
        have invC' : invcat (C_without_z z), from C_without_z_invcat z,        
        have finC' : C_without_z z ≃ₛ fin n', from @C_without_z_is_finite _ _ _ _,
        

        -- using equivalences
        apply equiv_is_fibrant,
        apply equiv.symm nat_unit_sigma_equiv,

        let q := matching_obj_map X z,
        have fibration_q : (is_fibration_alt q), from rfib z,

        let p := map_L_to_Mz_alt z X,
        apply equiv_is_fibrant, apply equiv.symm,

        calc
                (Σ (c : Π y, X y), Π y y' f, morphism X f (c y) = c y')
             ≃ₛ (Σ (c_z : X z) (c : (Π y : C_without_z z, X y)),
                 (Π (y : C_without_z z) (f : z ⟶ obj y ), X f c_z = c y) × (Π (y y' : C_without_z z)
                 (f : @hom (subcat_obj _ _) _ y y'), (Functor_from_C' z X) f (c y) = c y')) : limit_two_piece_limit_equiv ψ idrefl z_max_φ
                 -- get a pullback of the span (L --p--> matching_object M Z <<--q-- X z)
                 -- where L is limit of X restricted to C_without_z (so, L is Nat(𝟙,Functor_from_C' z X))
         ... ≃ₛ (Σ (c_z : X z) d, p d = q c_z) : two_piece_limit_pullback_p_q_equiv
         ... ≃ₛ (Σ d (c_z : X z), p d = q c_z) : equiv.sigma_swap
         ... ≃ₛ (Σ d (c_z : X z), q c_z = p d) : by apply @sigma_congr₂; intros; apply @sigma_congr₂; intros; 
                                                     apply (iff_impl_equiv (iff.intro eq.symm eq.symm)),

        -- to show that this pullback is fibrant we use facts that q is a fibration (from Reedy fibrancy of X) and
        -- that L is fibrant (from IH)
        have rfibX' : is_reedy_fibrant (Functor_from_C' z X), from @Functor_from_C'_reedy_fibrant _ z X _ φ z_max_φ idrefl rfib ⟨_,ψ⟩,
        assert isFibL: is_fibrant (lim_restricted X z),
          begin
          refine (@equiv_is_fibrant _ _ nat_unit_sigma_equiv _), apply IHn, apply rfibX', apply finC'
          end,
        refine @fibration_domain_is_fibrant _ (Fib.mk _ isFibL) (λpb, pb.1) _,
        refine Pullback'_is_fibrant q p, apply fibration_q
      }
    end
end fiblimits
