import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.Covering
import PoincareConjecture.Proofs.Horizon.Topology.Covering.Quotient.Properness









set_option autoImplicit false

open Function Set Topology

namespace Poincare.Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}



theorem exists_covering_transformation [SimplyConnectedSpace E]
    [LocallyPathConnectedSpace E] (hp : IsCoveringMap p)
    (e₀ e₁ : E) (he : p e₀ = p e₁) :
    ∃ d : E ≃ₜ E, p ∘ d = p ∧ d e₀ = e₁ := by
  obtain ⟨F, ⟨hF₀, hF⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts ⟨p, hp.continuous⟩ e₀ e₁ he.symm
  obtain ⟨G, ⟨hG₁, hG⟩, _⟩ :=
    hp.existsUnique_continuousMap_lifts ⟨p, hp.continuous⟩ e₁ e₀ he
  have hGF : G ∘ F = id := hp.eq_of_comp_eq
    (G.continuous.comp F.continuous) continuous_id
    (by ext e; exact (congr_fun hG (F e)).trans (congr_fun hF e))
    e₀ (by change G (F e₀) = e₀; rw [hF₀, hG₁])
  have hFG : F ∘ G = id := hp.eq_of_comp_eq
    (F.continuous.comp G.continuous) continuous_id
    (by ext e; exact (congr_fun hF (G e)).trans (congr_fun hG e))
    e₁ (by change F (G e₁) = e₁; rw [hG₁, hF₀])
  let d : E ≃ₜ E :=
    { toFun := F
      invFun := G
      left_inv := congr_fun hGF
      right_inv := congr_fun hFG
      continuous_toFun := F.continuous
      continuous_invFun := G.continuous }
  exact ⟨d, hF, hF₀⟩



theorem exists_nonidentity_covering_transformation [SimplyConnectedSpace E]
    [LocallyPathConnectedSpace E] (hp : IsCoveringMap p) (hsurj : Surjective p)
    (hbase : ¬ SimplyConnectedSpace X) :
    ∃ d : E ≃ₜ E, p ∘ d = p ∧ d ≠ Homeomorph.refl E := by
  have hni : ¬ Injective p := by
    intro hinj
    exact hbase (hp.isLocalHomeomorph.toHomeomorphOfBijective
      ⟨hinj, hsurj⟩).symm.toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨e₀, e₁, he, hne⟩ := Function.not_injective_iff.mp hni
  obtain ⟨d, hd, hde⟩ := exists_covering_transformation hp e₀ e₁ he
  refine ⟨d, hd, ?_⟩
  intro h
  exact hne (by simpa only [h, Homeomorph.refl_apply, id_eq] using hde)


def deckTransformations (p : E → X) : Subgroup (E ≃ₜ E) where
  carrier := {d | p ∘ d = p}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    ext e
    exact (congr_fun ha (b e)).trans (congr_fun hb e)
  inv_mem' := by
    intro a ha
    ext e
    simpa only [comp_apply, Homeomorph.inv_apply, Homeomorph.apply_symm_apply] using
      (congr_fun ha (a.symm e)).symm

instance deckTransformations_mulAction : MulAction (deckTransformations p) E where
  smul d e := d.1 e
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

instance deckTransformations_continuousConstSMul :
    ContinuousConstSMul (deckTransformations p) E where
  continuous_const_smul d := d.1.continuous


theorem deckTransformations_isCancelSMul [PreconnectedSpace E] (hp : IsCoveringMap p) :
    IsCancelSMul (deckTransformations p) E where
  right_cancel' a b e he := by
    apply Subtype.ext
    apply Homeomorph.ext
    exact congr_fun (hp.eq_of_comp_eq a.1.continuous b.1.continuous
      (a.2.trans b.2.symm) e he)



theorem finite_deckTransformations_mem_compact [PreconnectedSpace E] [T1Space X]
    (hp : IsCoveringMap p) (e : E) {K : Set E} (hK : IsCompact K) :
    {d : deckTransformations p | d.1 e ∈ K}.Finite := by
  let : DiscreteTopology (p ⁻¹' {p e}) := (hp (p e)).discreteTopology_fiber
  have hclosed : IsClosed (p ⁻¹' {p e}) := isClosed_singleton.preimage hp.continuous
  have hfin : ((Subtype.val : (p ⁻¹' {p e}) → E) ⁻¹' K).Finite :=
    (hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hK).finite_of_discrete
  let f : deckTransformations p → (p ⁻¹' {p e}) :=
    fun d => ⟨d.1 e, congr_fun d.2 e⟩
  have hinj : Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Homeomorph.ext
    exact congr_fun (hp.eq_of_comp_eq a.1.continuous b.1.continuous
      (a.2.trans b.2.symm) e (congr_arg Subtype.val hab))
  have hh := Set.Finite.preimage (f := f) hinj.injOn hfin
  exact hh



theorem isQuotientCoveringMap_deckTransformations [SimplyConnectedSpace E]
    [LocallyPathConnectedSpace E] (hp : IsCoveringMap p) (hsurj : Surjective p) :
    IsQuotientCoveringMap p (deckTransformations p) := by
  rw [isQuotientCoveringMap_iff_isCoveringMap_and]
  refine ⟨hp, hsurj, inferInstance, deckTransformations_isCancelSMul hp, ?_⟩
  intro e₁ e₂
  constructor
  · intro he
    obtain ⟨d, hd, hde⟩ := exists_covering_transformation hp e₂ e₁ he.symm
    exact ⟨⟨d, hd⟩, hde⟩
  · rintro ⟨d, hd⟩
    rw [← hd]
    exact congr_fun d.2 e₂



theorem deckTransformations_properlyDiscontinuousSMul [SimplyConnectedSpace E]
    [LocallyPathConnectedSpace E] [T2Space X]
    (hp : IsCoveringMap p) (hsurj : Surjective p) :
    ProperlyDiscontinuousSMul (deckTransformations p) E :=
  (isQuotientCoveringMap_deckTransformations hp hsurj).properlyDiscontinuousSMul


theorem finite_deckTransformations_inter_compact [SimplyConnectedSpace E]
    [LocallyPathConnectedSpace E] [T2Space X]
    (hp : IsCoveringMap p) (hsurj : Surjective p)
    {K L : Set E} (hK : IsCompact K) (hL : IsCompact L) :
    {d : deckTransformations p | (d.1 '' K ∩ L).Nonempty}.Finite := by
  let := deckTransformations_properlyDiscontinuousSMul hp hsurj
  exact finite_disjoint_inter_image hK hL



theorem locallyFinite_deck_translates_compact [SimplyConnectedSpace E]
    [LocallyPathConnectedSpace E] [LocallyCompactSpace E] [T2Space X]
    (hp : IsCoveringMap p) (hsurj : Surjective p) {K : Set E} (hK : IsCompact K) :
    LocallyFinite (fun d : deckTransformations p => d.1 '' K) := by
  intro e
  obtain ⟨L, hL, heL⟩ := exists_compact_mem_nhds e
  exact ⟨L, heL, finite_deckTransformations_inter_compact hp hsurj hK hL⟩

end Poincare.Topology
