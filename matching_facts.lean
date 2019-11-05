import algebra.category
import inverse limit fibrant finite matching

open sigma category eq.ops function functor

open reduced_coslice invcat

section MO_facts
   variables {C : Category.{1 1}}
             {D : Category}

    open reduced_coslice reduced_coslice.coslice_obs nat subcat_obj fincat matching_object invcat
    open equiv equiv.ops poly_unit
    open natural_transformation

    variables {z : C} {x : C_without_z z}
              {φ : C ⇒ ℕop} {reflecting_id : id_reflect φ}
              {max_rank : ∀ x, φ x ≤ φ z}
              [is_obj_finite C] [invcat C]
              (X : C ⇒ Uₛ)

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
