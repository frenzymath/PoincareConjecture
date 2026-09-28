import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CrossRayTangents
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Boundary.FanAngles




noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold Matrix

namespace PoincareConjecture




theorem m64Intrinsic_unit_tangents_independent
    (G : RiemannianMetric 2 AnnulusCoordinates) (p v w : AnnulusCoordinates)
    (hv : G.inner p v v = 1) (hw : G.inner p w w = 1)
    (hne : v ≠ w) (hopp : v ≠ -w) :
    LinearIndependent ℝ (![v, w] : Fin 2 → AnnulusCoordinates) := by
  have hwn : w ≠ 0 := by
    intro hz
    simp only [hz, map_zero] at hw
    exact zero_ne_one hw
  rw [linearIndependent_fin2]
  refine ⟨hwn, ?_⟩
  intro c hc
  change c • w = v at hc
  have hsq : c ^ 2 = 1 := by
    rw [← hc] at hv
    simp only [map_smul, smul_apply, smul_eq_mul, hw] at hv
    nlinarith only [hv]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp
      (show c ^ 2 = (1 : ℝ) ^ 2 by simpa only [one_pow] using hsq) with rfl | rfl
  · exact hne (by simpa only [one_smul] using hc.symm)
  · exact hopp (by simpa only [neg_one_smul] using hc.symm)




theorem m64Intrinsic_unit_tangent_angle_bounds
    (G : RiemannianMetric 2 AnnulusCoordinates) (p v w : AnnulusCoordinates)
    (hv : G.inner p v v = 1) (hw : G.inner p w w = 1)
    (hne : v ≠ w) (hopp : v ≠ -w) :
    0 < G.cornerAngle p v w ∧ G.cornerAngle p v w < Real.pi := by
  have hminus := G.pos p (v - w) (sub_ne_zero.mpr hne)
  have hplus := G.pos p (v + w) (fun h => hopp (eq_neg_of_add_eq_zero_left h))
  simp only [map_sub, sub_apply, map_add, add_apply, hv, hw, G.symm p w v] at hminus hplus
  simp only [RiemannianMetric.cornerAngle, hv, hw, Real.sqrt_one, inv_one, one_smul]
  exact ⟨Real.arccos_pos.mpr (by linarith only [hminus]),
    Real.arccos_lt_pi.mpr (by linarith only [hplus])⟩

end PoincareConjecture
