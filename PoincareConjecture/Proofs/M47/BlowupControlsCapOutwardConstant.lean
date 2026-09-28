import PoincareConjecture.Proofs.M47.BlowupControlsCapOutwardTopology
import PoincareConjecture.Proofs.M34.Standard.NeckHeightControlBarrier

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

theorem cap_core_to_axial_intrinsic_lower {c d b : ℝ}
    (hc : -N.epsilon⁻¹ < c) (hcd : c < d) (hdb : d < b)
    (hb : b < N.epsilon⁻¹) {o : M} (ho : o ∈ N.closed_core)
    (q : UnitTwoSphere) :
    ENNReal.ofReal ((b - d) * N.end_neck.scale / 2) ≤
      intrinsicEDist g N.carrier o (N.end_neck.coordinate_map (q, b)) := by
  have hA : 0 < 2 / N.end_neck.scale := div_pos (by norm_num) N.end_neck.scale_pos
  have hfront : N.end_neck.coordinate_map (q, b) ∈ frontier (N.recutCarrier b) := by
    rw [N.recutCarrier_frontier_eq_axial_sphere (hc.trans (hcd.trans hdb)) hb]
    exact mem_image_of_mem _ ⟨mem_univ _, rfl⟩
  apply le_sInf
  rintro L ⟨gamma, hgamma, hstart, hfinish, hmem, rfl⟩
  have hbarrier := N.collar_height_le_pathELength hc hcd hdb hb zero_le_one hgamma
    (fun s hs => hmem (mem_image_of_mem gamma hs)) (hstart.symm ▸ ho)
    (hfinish.symm ▸ hfront)
  have h := (ENNReal.div_le_iff' (ENNReal.ofReal_pos.mpr hA).ne'
    ENNReal.ofReal_ne_top).mpr hbarrier
  rw [← ENNReal.ofReal_div_of_pos hA] at h
  have heq : (b - d) * N.end_neck.scale / 2 = (b - d) / (2 / N.end_neck.scale) := by
    field_simp [N.end_neck.scale_pos.ne']
  rw [heq]
  exact h

private theorem cap_scalarSup_rpow_le_end_scale :
    scalarCurvatureSupOn g N.connection N.carrier ^ (-1 / 2 : ℝ) ≤ N.end_neck.scale := by
  have hc : N.end_neck.center ∈ N.carrier :=
    N.end_neck_subset (N.end_neck.central_sphere_subset N.end_neck.center_on_central_sphere)
  obtain ⟨k, _, hratio⟩ := N.scalar_ratio
  have hbounded : BddAbove (range (fun z : N.carrier => N.connection.scalarCurvature z)) :=
    ⟨k * N.connection.scalarCurvature N.end_neck.center, by
      rintro _ ⟨z, rfl⟩
      exact hratio _ hc z z.2⟩
  have hle : N.connection.scalarCurvature N.end_neck.center ≤
      scalarCurvatureSupOn g N.connection N.carrier :=
    le_csSup hbounded ⟨⟨N.end_neck.center, hc⟩, rfl⟩
  have hpow := Real.rpow_le_rpow_of_nonpos (N.scalar_pos _ hc) hle
    (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  rw [N.end_neck.scale_eq_scalar, N.end_neck_connection]
  exact hpow

theorem cap_inverse_accuracy_lt_constant :
    (3 / 4 : ℝ) * N.epsilon⁻¹ < N.cap_constant := by
  have he : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  let c := -(7 / 8 : ℝ) * N.epsilon⁻¹
  let d := -(3 / 4 : ℝ) * N.epsilon⁻¹
  let b := (3 / 4 : ℝ) * N.epsilon⁻¹
  have hc : -N.epsilon⁻¹ < c := by dsimp [c]; linarith
  have hcd : c < d := by dsimp [c, d]; linarith
  have hdb : d < b := by dsimp [d, b]; linarith
  have hb : b < N.epsilon⁻¹ := by dsimp [b]; linarith
  obtain ⟨o, ho⟩ := N.core_nonempty
  have hoc := interior_subset (N.core_eq_interior_closed_core ▸ ho)
  let q := (N.end_neck.coordinate_inverse N.end_neck.center).1
  have hz : b ∈ Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
    rw [N.end_neck_epsilon]
    exact ⟨hc.trans (hcd.trans hdb), hb⟩
  have hxc : N.end_neck.coordinate_map (q, b) ∈ N.carrier :=
    N.end_neck_subset (N.end_neck.coordinate_map_mem_of_axial_mem hz)
  have hdist := cap_core_to_axial_intrinsic_lower N hc hcd hdb hb hoc q
  have hdiam := hdist.trans (intrinsicEDist_le_intrinsicDiameter
    (N.closed_core_subset_carrier hoc) hxc)
  have hupper : intrinsicDiameter g N.carrier <
      ENNReal.ofReal (N.cap_constant * N.end_neck.scale) :=
    N.intrinsic_diameter_bound.trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (cap_scalarSup_rpow_le_end_scale N) N.cap_constant_pos.le))
  have hreal := (ENNReal.ofReal_lt_ofReal_iff
    (mul_pos N.cap_constant_pos N.end_neck.scale_pos)).mp (hdiam.trans_lt hupper)
  dsimp [b, d] at hreal
  nlinarith [N.end_neck.scale_pos]

theorem cap_constant_gt_nine_hundred (hsmall : N.epsilon ≤ 1 / 1200) :
    (900 : ℝ) < N.cap_constant := by
  have hinv : (1200 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := inv_anti₀ N.epsilon_pos hsmall
    norm_num at h
    exact h
  have h := cap_inverse_accuracy_lt_constant N
  linarith

end PoincareConjecture.M47
