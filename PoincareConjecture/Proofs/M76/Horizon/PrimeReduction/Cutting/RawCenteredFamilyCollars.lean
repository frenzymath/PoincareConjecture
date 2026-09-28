import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.RawCenteredProductCollar

set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem exists_signed_collars_of_centered_family
    {X κ : Type*} [TopologicalSpace X] [T2Space X] {R Q : Set X}
    (S O : κ → Set X) (hS : ∀ i, IsCompact (S i))
    (W : ∀ i, (S i × unitInterval) ≃ₜ closure (O i))
    (hQ : Q = R \ ⋃ i, O i)
    (hO : ∀ i, IsOpen (O i)) (hOR : ∀ i, closure (O i) ⊆ R)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hSC : ∀ i, S i ⊆ closure (O i))
    (hopen : ∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hcenter : ∀ i z, (W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1/2) :
    ∃ (HB : ∀ i, S i ≃ₜ S i) (c : κ → X × ℝ → X),
      (∀ i, ContinuousOn (c i) (S i ×ˢ Icc (-1 : ℝ) 1)) ∧
      (∀ i, Topology.IsEmbedding
        (fun z : (S i ×ˢ Icc (-1 : ℝ) 1 : Set (X × ℝ)) => c i z)) ∧
      (∀ i (z : S i), c i ((z : X),0) = (HB i z : X)) ∧
      (∀ i, c i '' (S i ×ˢ Ioo (-1 : ℝ) 1) = O i) ∧
      (∀ i, IsOpen (c i '' (S i ×ˢ Ioo (-1 : ℝ) 1))) ∧
      (∀ i (b : Bool), c i '' (S i ×ˢ ({if b then (1 : ℝ) else -1} : Set ℝ)) ⊆ Q) ∧
      Disjoint (⋃ i, S i) Q := by
  classical
  choose HB c hc hi hzero hopenEq hclosedEq hend hSO using
    fun i => exists_signed_collar_of_centered_product (hS i) (W i) (hO i) (hSC i)
      (hopen i) (hcenter i)
  refine ⟨HB,c,hc,hi,hzero,hopenEq,fun i => (hopenEq i).symm ▸ hO i,?_,?_⟩
  · intro i b x hx
    have hxF := hend i b hx
    rw [hQ]
    refine ⟨hOR i (frontier_subset_closure hxF),?_⟩
    intro hxO
    obtain ⟨j,hj⟩ := mem_iUnion.mp hxO
    by_cases hji : j = i
    · exact hxF.2 ((hO i).interior_eq.symm ▸ (hji ▸ hj))
    · exact disjoint_left.mp (hdis (Ne.symm hji))
        (frontier_subset_closure hxF) (subset_closure hj)
  · apply disjoint_left.mpr
    intro x hxS hxQ
    obtain ⟨i,hi⟩ := mem_iUnion.mp hxS
    exact (hQ.subset hxQ).2 (mem_iUnion.mpr ⟨i,hSO i hi⟩)

end PoincareConjecture.M76
