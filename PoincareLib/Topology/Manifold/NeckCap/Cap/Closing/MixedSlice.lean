import PoincareLib.Topology.Manifold.NeckCap.Cap.Growth.MixedBoundary
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ReciprocalStrip

/-!
# Shifted boundary spheres for mixed cap overlap

An original boundary sphere meeting a cap without lying in it crosses its
positive frontier. The reciprocal neck estimate places a whole shifted
boundary slice inside the cap's end. The shift and threshold are uniform.

Reference: Morgan--Tian, Claims A.23--A.24, pp. 512--513.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.CapCertificate

/-- Mixed boundary overlap produces an actual whole shifted sphere in the
first cap's end, using the two original neck certificates. -/
theorem exists_mixed_boundary_shifted_slice_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 10000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (C D : CapCertificate g), C.epsilon ≤ ε₀ → D.epsilon = C.epsilon →
          (D.boundary_sphere ∩ C.carrier).Nonempty →
          (¬ D.boundary_sphere ⊆ C.carrier) →
          ∃ a : ℝ, |a| = (0.05 : ℝ) * C.epsilon⁻¹ ∧
            a ∈ Ioo (-D.boundary_neck.epsilon⁻¹) D.boundary_neck.epsilon⁻¹ ∧
            range (fun q : UnitTwoSphere => D.boundary_neck.coordinate_map (q, a)) ⊆
              C.end_neck.region ((0.9 : ℝ) * C.epsilon⁻¹) C.epsilon⁻¹ := by
  obtain ⟨ε₁, hε₁, _, hcontact⟩ := exists_mixed_boundary_positive_end_contact.{u}
  obtain ⟨ε₂, hε₂, hsmall, hslice⟩ :=
    EpsilonNeck.exists_shifted_slice_subset_positive_end_of_frontier_contact.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_right _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g C D hC hDC hmeet hmiss
  obtain ⟨x, _, hxfront, hxquarter, hxD⟩ :=
    hcontact C D (hC.trans (min_le_left _ _)) hmeet hmiss
  obtain ⟨σ, hσ, hsub⟩ := hslice C.end_neck D.boundary_neck
    (C.end_neck_epsilon.trans_le (hC.trans (min_le_right _ _)))
    (D.boundary_neck_epsilon.trans (hDC.trans C.end_neck_epsilon.symm)) x hxfront
    (by simpa only [C.end_neck_epsilon] using hxquarter) hxD
  have hR : 0 < C.epsilon⁻¹ := inv_pos.mpr C.epsilon_pos
  have hshift : 0 < (0.05 : ℝ) * C.epsilon⁻¹ := mul_pos (by norm_num) hR
  refine ⟨σ * (0.05 : ℝ) * C.epsilon⁻¹, ?_, ?_, ?_⟩
  · rcases hσ with rfl | rfl
    · simp only [one_mul, abs_of_pos hshift]
    · rw [neg_one_mul, neg_mul, abs_neg, abs_of_pos hshift]
  · rw [D.boundary_neck_epsilon, hDC]
    rcases hσ with rfl | rfl <;> constructor <;> nlinarith
  · simpa only [C.end_neck_epsilon] using hsub

end PoincareMT.CapCertificate
