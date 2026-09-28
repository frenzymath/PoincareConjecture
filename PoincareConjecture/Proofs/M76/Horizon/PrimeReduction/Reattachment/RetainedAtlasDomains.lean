import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.GlobalPulledBackAtlas










set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.transfer_of_retained_charts
    {X ι κ : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (a : κ → OpenPartialHomeomorph X V3) {R E O : Set X}
    (he : PLDomain e R) (ha : PLDomain a E)
    (hO : IsOpen O) (hfront : frontier R ⊆ O)
    (r : ι → κ) (hret : ∀ i, a (r i) = (e i).restrOpen O hO) :
    PLDomain a R ∧
      ChartwisePLOn e a (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' O) ∧
      ChartwisePLOn a e (ContinuousMap.id R) ((Subtype.val : R → X) ⁻¹' O) ∧
      ChartwisePLOn e a (ContinuousMap.id (univ : Set X))
        ((Subtype.val : ↥(univ : Set X) → X) ⁻¹' O) ∧
      ChartwisePLOn a e (ContinuousMap.id (univ : Set X))
        ((Subtype.val : ↥(univ : Set X) → X) ⁻¹' O) := by
  let old := fun i => (e i).restrOpen O hO
  have hcross (i : ι) (j : κ) :
      ((e i).restrOpen O hO).symm.trans (a j) ∈ piecewiseAffineGroupoid V3 := by
    rw [← hret i]
    exact ha.compatible (r i) j
  have hrestrict (c d : OpenPartialHomeomorph X V3)
      (h : c.symm.trans d ∈ piecewiseAffineGroupoid V3) :
      (c.restrOpen O hO).symm.trans (d.restrOpen O hO) ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact h.1.mono ((c.restrOpen O hO).symm.trans (d.restrOpen O hO)).open_source
      (fun _ hx => ⟨hx.1.1, hx.2.1⟩)
  have haR : PLDomain a R := by
    refine ⟨ha.cover, ha.compatible, he.closed, ?_⟩
    intro x hx
    obtain ⟨ell, v, B, hv, hxB, hzero, hB, hhalf⟩ := he.halfspace x hx
    refine ⟨ell, v, B.restrOpen O hO, hv, ⟨hxB, hfront hx⟩, hzero, ?_, ?_⟩
    · intro j
      apply pl_transition_mem_of_overlap_cover old
      · intro y hy
        obtain ⟨i, hi⟩ := he.cover y
        exact ⟨i, hi, hy.2.2⟩
      · intro i
        exact hcross i j
      · intro i
        exact hrestrict _ _ (hB i)
    · intro y hy
      exact hhalf y hy.1
  obtain ⟨hforward, hreverse⟩ :=
    chartwisePLOn_identity_domain_both_of_restricted_transitions e a he haR hO hcross
  have heU : PLDomain e (univ : Set X) := by
    refine ⟨he.cover, he.compatible, isClosed_univ, ?_⟩
    simp only [frontier_univ, mem_empty_iff_false, forall_false, implies_true]
  have haU : PLDomain a (univ : Set X) := by
    refine ⟨ha.cover, ha.compatible, isClosed_univ, ?_⟩
    simp only [frontier_univ, mem_empty_iff_false, forall_false, implies_true]
  obtain ⟨hambient, hambient'⟩ :=
    chartwisePLOn_identity_domain_both_of_restricted_transitions e a heU haU hO hcross
  exact ⟨haR, hforward, hreverse, hambient, hambient'⟩

end PoincareConjecture.M76
