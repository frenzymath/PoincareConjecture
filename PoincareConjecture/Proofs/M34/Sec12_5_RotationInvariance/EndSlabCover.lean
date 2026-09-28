import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndCompactSlabs

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)

theorem endClosedSlab_mono {a b c d : ℝ} (hac : c ≤ a) (hbd : b ≤ d) :
    endClosedSlab e a b ⊆ endClosedSlab e c d := by
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z, ⟨mem_univ _, hac.trans hz.2.1, hz.2.2.trans hbd⟩, rfl⟩

theorem endEnergyCutoff_eq_one_on_slab {x : StandardCapSpace}
    (hx : x ∈ endClosedSlab e (17 / 5) (23 / 5)) : endEnergyCutoff e x = 1 := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hl : (17 / 5 : ℝ) ≤ z.2 := hz.2.1
  have hu : z.2 ≤ (23 / 5 : ℝ) := hz.2.2
  apply endEnergyCutoff_eq_one e
  rw [endExhaustion_coordinate_of_two_le e (by linarith)]
  constructor <;> linarith

theorem endEnergyCutoff_tsupport_subset_three_slabs :
    tsupport (endEnergyCutoff e) ⊆
      (endClosedSlab e (31 / 10) (18 / 5) ∪ endClosedSlab e (17 / 5) (23 / 5)) ∪
        endClosedSlab e (22 / 5) (49 / 10) := by
  intro x hx
  obtain ⟨z, hz, rfl⟩ := endEnergyCutoff_tsupport_subset_slab e hx
  have hl : (31 / 10 : ℝ) ≤ z.2 := hz.2.1
  have hu : z.2 ≤ (49 / 10 : ℝ) := hz.2.2
  by_cases hlow : z.2 ≤ 18 / 5
  · exact Or.inl (Or.inl ⟨z, ⟨mem_univ _, hl, hlow⟩, rfl⟩)
  · by_cases hmid : z.2 ≤ 23 / 5
    · exact Or.inl (Or.inr ⟨z, ⟨mem_univ _, by linarith, hmid⟩, rfl⟩)
    · exact Or.inr ⟨z, ⟨mem_univ _, by linarith, hu⟩, rfl⟩

end PoincareConjecture.M34
