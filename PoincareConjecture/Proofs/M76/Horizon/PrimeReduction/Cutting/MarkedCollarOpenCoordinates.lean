import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.ClosedCutCollarCover

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

theorem mem_collar_endpoint_iff
    {X A : Type*} [TopologicalSpace X] [TopologicalSpace A]
    {C B : Set X} (W : (A × unitInterval) ≃ₜ C) (H : A ≃ₜ B)
    (t : unitInterval) (hW : ∀ a, (W (a, t) : X) = H a) (z : A × unitInterval) :
    (W z : X) ∈ B ↔ z.2 = t := by
  constructor
  · intro hz
    let a := H.symm ⟨W z, hz⟩
    have he : W (a, t) = W z := by
      apply Subtype.ext
      exact (hW a).trans (congrArg Subtype.val (H.apply_symm_apply ⟨W z, hz⟩))
    exact (congrArg Prod.snd (W.injective he)).symm
  · intro hz
    have he : z = (z.1, t) := Prod.ext rfl hz
    rw [he, hW]
    exact (H z.1).property

theorem marked_cut_collar_open_iff
    {X κ : Type*} [TopologicalSpace X]
    {A : κ → Type*} [∀ i, TopologicalSpace (A i)]
    (R Q : Set X) (O : κ → Set X) (B : κ × Bool → Set X)
    (W : ∀ i, (A i × unitInterval) ≃ₜ closure (O i))
    (H : ∀ i b, A i ≃ₜ B (i, b))
    (hQ : Q = R \ ⋃ i, O i)
    (hCR : ∀ i, closure (O i) ⊆ R)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hinc : ∀ i, closure (O i) ∩ Q = B (i, false) ∪ B (i, true))
    (hW : ∀ i a, (W i (a, 0) : X) = H i false a ∧
      (W i (a, 1) : X) = H i true a)
    (i : κ) (z : A i × unitInterval) :
    (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1 := by
  have hfamily : (W i z : X) ∈ ⋃ j, O j ↔ (W i z : X) ∈ O i := by
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      by_cases hij : i = j
      · exact hij ▸ hj
      · exact False.elim (disjoint_left.mp (hdis hij) (W i z).property
          (subset_closure hj))
    · exact fun hx => mem_iUnion.mpr ⟨i, hx⟩
  have hnot : (W i z : X) ∈ Q ↔ (W i z : X) ∉ O i := by
    rw [hQ]
    simp only [mem_sdiff, hCR i (W i z).property, true_and, hfamily]
  have hend : (W i z : X) ∈ Q ↔ z.2 = 0 ∨ z.2 = 1 := by
    have hb : (W i z : X) ∈ Q ↔
        (W i z : X) ∈ B (i, false) ∪ B (i, true) := by
      rw [← hinc]
      exact (and_iff_right (W i z).property).symm
    rw [hb, mem_union,
      mem_collar_endpoint_iff (W i) (H i false) 0 (fun a => (hW i a).1),
      mem_collar_endpoint_iff (W i) (H i true) 1 (fun a => (hW i a).2)]
  have hyes : (W i z : X) ∈ O i ↔ ¬ (z.2 = 0 ∨ z.2 = 1) := by
    rw [← hend, hnot, not_not]
  rw [hyes]
  constructor
  · intro hz
    have hz0 : (z.2 : ℝ) ≠ 0 := fun h => hz (Or.inl (Subtype.ext h))
    have hz1 : (z.2 : ℝ) ≠ 1 := fun h => hz (Or.inr (Subtype.ext h))
    exact ⟨lt_of_le_of_ne z.2.property.1 (Ne.symm hz0),
      lt_of_le_of_ne z.2.property.2 hz1⟩
  · rintro ⟨h0, h1⟩ (hz | hz)
    · have h : (z.2 : ℝ) = 0 := congrArg Subtype.val hz
      linarith
    · have h : (z.2 : ℝ) = 1 := congrArg Subtype.val hz
      linarith

end PoincareConjecture.M76
