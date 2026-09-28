import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_SeedCurvature
import PoincareConjecture.Definitions.M28BoundedDistance

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

noncomputable def blowupPinchingThreshold (K eta : ℝ) : ℝ :=
  max (Real.exp 4) (Real.exp (4 + K / (2 * eta)) / eta)

theorem negative_part_le_blowup_error {K eta Q R X t : ℝ}
    (hK : 0 ≤ K) (heta : 0 < eta) (hQ : blowupPinchingThreshold K eta ≤ Q)
    (ht : 0 ≤ t) (hR : R ≤ K * Q)
    (hpinch : 0 < X →
      2 * X * (Real.log X + Real.log (1 + t) - 3) ≤ R) : X ≤ eta * Q := by
  have hQpos : 0 < Q :=
    (Real.exp_pos 4).trans_le ((le_max_left _ _).trans hQ)
  by_contra hnot
  have hX : eta * Q < X := lt_of_not_ge hnot
  have hXpos : 0 < X := (mul_pos heta hQpos).trans hX
  have hexp : Real.exp (4 + K / (2 * eta)) ≤ eta * Q := by
    have h := (div_le_iff₀ heta).mp ((le_max_right _ _).trans hQ)
    simpa only [mul_comm] using h
  have hlog : 4 + K / (2 * eta) ≤ Real.log X := by
    simpa only [Real.log_exp] using
      (Real.log_le_log_iff (Real.exp_pos _) hXpos).mpr (hexp.trans hX.le)
  have hlogt : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  have hquotient : 0 ≤ K / (2 * eta) := div_nonneg hK (by positivity)
  have hfactor : 0 < 1 + K / (2 * eta) := by linarith
  have hreaction : 2 * X * (1 + K / (2 * eta)) ≤ R :=
    (mul_le_mul_of_nonneg_left (by linarith :
      1 + K / (2 * eta) ≤ Real.log X + Real.log (1 + t) - 3)
      (by positivity : 0 ≤ 2 * X)).trans (hpinch hXpos)
  have hstrict : 2 * (eta * Q) * (1 + K / (2 * eta)) < K * Q :=
    (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hX (by norm_num)) hfactor).trans_le
      (hreaction.trans hR)
  have hid : 2 * (eta * Q) * (1 + K / (2 * eta)) = K * Q + 2 * eta * Q := by
    field_simp [heta.ne']
    ring
  rw [hid] at hstrict
  nlinarith [mul_pos heta hQpos]

theorem pinched_blowup_curvature_bounds (P : M46Predecessors.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {D : LeviCivitaData g}
    {U : Set M} {t K eta Q : ℝ} (hPinched : SurgeryPinchedOn D t U)
    (hK : 0 ≤ K) (heta : 0 < eta) (hQ : blowupPinchingThreshold K eta ≤ Q)
    {x : M} (hx : x ∈ U) (hScalar : D.scalarCurvature x ≤ K * Q) :
    |D.curvatureTensorNorm x| ≤ (13 * max K 1) * Q ∧
      D.negativeCurvaturePart x ≤ eta * Q := by
  have hQexp : Real.exp 4 ≤ Q := (le_max_left _ _).trans hQ
  have hQpos : 0 < Q := (Real.exp_pos 4).trans_le hQexp
  have hScalar' : D.scalarCurvature x ≤ max K 1 * Q :=
    hScalar.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hQpos.le)
  have hExp : Real.exp 4 ≤ max K 1 * Q := hQexp.trans (by
    nlinarith [le_max_right K 1])
  constructor
  · rw [abs_of_nonneg (show 0 ≤ D.curvatureTensorNorm x from Real.sqrt_nonneg _)]
    have h := (Proofs.M46.pinched_curvature_norm_le P hPinched hx).trans
      (mul_le_mul_of_nonneg_left (max_le hScalar' hExp) (by norm_num : (0 : ℝ) ≤ 13))
    simpa only [mul_assoc] using h
  · exact negative_part_le_blowup_error hK heta hQ hPinched.1 hScalar
      (hPinched.2.2 x hx)

theorem generalized_blowup_curvature_bounds (P : M46Predecessors.{u})
    (G : GeneralizedRicciFlowData.{u}) (hPinched : generalizedHamiltonIveyPinched G)
    {t K eta Q : ℝ} (ht : t ∈ G.interval) (hK : 0 ≤ K) (heta : 0 < eta)
    (hQ : blowupPinchingThreshold K eta ≤ Q) {x : (G.slice t).carrier}
    (hScalar : G.scalar ⟨t, x⟩ ≤ K * Q) :
    |G.curvatureNorm ⟨t, x⟩| ≤ (13 * max K 1) * Q ∧
      (G.connection t).negativeCurvaturePart x ≤ eta * Q := by
  have hp := hPinched t ht
  have hphysical : SurgeryPinchedAt (G.connection t) t :=
    ⟨hp.2.1, fun y _ => hp.2.2.1 y, fun y _ => hp.2.2.2 y⟩
  exact pinched_blowup_curvature_bounds P hphysical hK heta hQ (mem_univ x) hScalar

end PoincareConjecture.M47
