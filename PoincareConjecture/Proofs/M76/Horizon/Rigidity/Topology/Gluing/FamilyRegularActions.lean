import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Gluing.CompatibleFaithfulActions

set_option autoImplicit false

namespace PoincareConjecture.M76.IncompressibleGluing

universe u

variable {I K : Type u} (G : I → Type u) (J : K → Type u)
  [∀ i, Group (G i)] [∀ k, Group (J k)]

def coordinateRegularAction [DecidableEq I] (i : I) :
    G i →* Equiv.Perm (∀ j, G j) where
  toFun g :=
    { toFun := fun p => Function.update p i (g * p i)
      invFun := fun p => Function.update p i (g⁻¹ * p i)
      left_inv := by
        intro p
        funext j
        by_cases hj : j = i
        · subst j; simp
        · simp [Function.update_of_ne hj]
      right_inv := by
        intro p
        funext j
        by_cases hj : j = i
        · subst j; simp
        · simp [Function.update_of_ne hj] }
  map_one' := by
    apply Equiv.ext
    intro p
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp
  map_mul' g h := by
    apply Equiv.ext
    intro p
    funext j
    by_cases hj : j = i
    · subst j; simp [mul_assoc]
    · simp [Function.update_of_ne hj]

theorem coordinateRegularAction_injective [DecidableEq I] (i : I) :
    Function.Injective (coordinateRegularAction G i) := by
  intro g h heq
  have := congrArg (fun e : Equiv.Perm (∀ j, G j) => e (fun _ => 1) i) heq
  simpa [coordinateRegularAction] using this

theorem exists_family_regular_action_exchange [DecidableEq I] [DecidableEq K]
    {H : Type u} [Group H] (i : I) (k : K)
    (f : H →* G i) (g : H →* J k)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ c : Equiv.Perm ((∀ j, G j) × (∀ l, J l)),
      ∀ h (p : (∀ j, G j) × (∀ l, J l)),
        c (Function.update p.1 i (f h * p.1 i), p.2) =
          ((c p).1, Function.update (c p).2 k (g h * (c p).2 k)) := by
  classical
  obtain ⟨c₂, hc₂⟩ := exists_regular_action_exchange f g hf hg
  let E := (Equiv.prodCongr (Equiv.piSplitAt i G) (Equiv.piSplitAt k J)).trans
    (Equiv.prodProdProdComm _ _ _ _)
  let c := E.trans ((Equiv.prodCongr c₂ (Equiv.refl _)).trans E.symm)
  have hE (p : (∀ j, G j) × (∀ l, J l)) :
      E (c p) = (c₂ (E p).1, (E p).2) := by
    exact E.apply_symm_apply _
  have hfirst (h : H) (p : (∀ j, G j) × (∀ l, J l)) :
      E (Function.update p.1 i (f h * p.1 i), p.2) =
        ((f h * (E p).1.1, (E p).1.2), (E p).2) := by
    refine Prod.ext (Prod.ext ?_ rfl) (Prod.ext ?_ rfl)
    · exact Function.update_self _ _ _
    · funext j
      exact Function.update_of_ne j.property _ _
  have hsecond (h : H) (p : (∀ j, G j) × (∀ l, J l)) :
      E (p.1, Function.update p.2 k (g h * p.2 k)) =
        (((E p).1.1, g h * (E p).1.2), (E p).2) := by
    refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)
    · exact Function.update_self _ _ _
    · funext j
      exact Function.update_of_ne j.property _ _
  refine ⟨c, ?_⟩
  intro h p
  apply E.injective
  rw [hE, hfirst, hsecond, hE]
  exact Prod.ext (hc₂ h (E p).1) rfl

end PoincareConjecture.M76.IncompressibleGluing
