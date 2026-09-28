import PoincareConjecture.Proofs.M35.CapGeometry.InitialNeckScalar
import PoincareConjecture.Definitions.M35StandardCapUniqueness

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

theorem exists_initial_slab_scalar_control {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta eta : ℝ}
    (htheta : theta ∈ Ico 0 E.flow.base.lifetime) (heta : 0 < eta) :
    ∃ K : Set StandardCapSpace, IsCompact K ∧
      ∀ x ∉ K, ∀ t ∈ Icc 0 theta,
        |(1 - t) * (E.flow.connection t).scalarCurvature x - 1| < eta := by
  have hthetaone : theta < 1 := E.lifetime_one ▸ htheta.2
  obtain ⟨delta, hdelta, hcontrol⟩ := exists_initial_cylinder_scalar_control hthetaone heta
  obtain ⟨A⟩ := E.asymptotic theta htheta delta hdelta
  refine ⟨A.compact_set, A.compact, ?_⟩
  intro x hx t ht
  obtain ⟨N, hN⟩ := A.patches x hx
  obtain ⟨q, hq⟩ := N.center_sphere
  have hfamily : RoundCylinderFamilyClose delta (Icc 0 theta)
      (fun u => roundCylinderPullback (E.flow.metric u) N.coordinate) := by
    simpa only [StandardSpacetimeCylinderClose, div_one, zero_add, one_mul] using hN
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := hfamily
  have hscalar := hcontrol delta hdelta le_rfl t ht (E.flow.metric t)
    (E.flow.connection t) x N q ⟨hsmooth t ht, bound, hbound, hjet t ht⟩
  simpa only [hq] using hscalar

theorem exists_initial_slab_scalar_bounds {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta : ℝ}
    (htheta : theta ∈ Ico 0 E.flow.base.lifetime) :
    ∃ K : Set StandardCapSpace, IsCompact K ∧
      ∀ x ∉ K, ∀ t ∈ Icc 0 theta,
        1 / 2 < (E.flow.connection t).scalarCurvature x ∧
          (E.flow.connection t).scalarCurvature x < 3 / (2 * (1 - theta)) := by
  obtain ⟨K, hK, hscalar⟩ := exists_initial_slab_scalar_control E htheta
    (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨K, hK, ?_⟩
  intro x hx t ht
  have h := abs_lt.mp (hscalar x hx t ht)
  have hthetaone : theta < 1 := E.lifetime_one ▸ htheta.2
  have htone : t < 1 := ht.2.trans_lt hthetaone
  have hR : 0 < (E.flow.connection t).scalarCurvature x := by
    have hh : 0 < (1 - t) * (E.flow.connection t).scalarCurvature x := by
      linarith only [h.1]
    exact pos_of_mul_pos_right hh (sub_pos.mpr htone).le
  have htR := mul_nonneg ht.1 hR.le
  refine ⟨by nlinarith only [h.1, htR], ?_⟩
  apply (lt_div_iff₀ (mul_pos (by norm_num) (sub_pos.mpr hthetaone))).mpr
  have hmon := mul_le_mul_of_nonneg_right (sub_le_sub_left ht.2 1) hR.le
  nlinarith only [h.2, hmon]

end PoincareConjecture.M35
