import PoincareConjecture.Proofs.M47.TerminalCurvatureStaticGeometry
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M47

theorem terminalCurvature_cap_target_scalar_comparison
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {X : Type v} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}
    (N : CapCertificate g) (D : LeviCivitaData h) (f : M → X)
    {C H : ℝ} (hC : N.cap_constant ≤ C) {x : M} (hx : x ∈ N.core)
    (hscalar : H ≤ N.connection.scalarCurvature x)
    (hxerror : |D.scalarCurvature (f x) - N.connection.scalarCurvature x| ≤
      H / (4 * max 1 C))
    (henderror : |D.scalarCurvature (f N.end_neck.center) -
      N.connection.scalarCurvature N.end_neck.center| ≤ H / (4 * max 1 C)) :
    0 < D.scalarCurvature (f N.end_neck.center) ∧
      D.scalarCurvature (f x) ≤
        (4 * max 1 C) * D.scalarCurvature (f N.end_neck.center) := by
  let A := max 1 C
  have hA1 : (1 : ℝ) ≤ A := le_max_left _ _
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have hend : N.end_neck.center ∈ N.carrier :=
    N.end_neck_subset (N.end_neck.central_sphere_subset N.end_neck.center_on_central_sphere)
  have hRend := N.scalar_pos _ hend
  have hcompare := terminalCurvature_cap_scalar_comparison N hx
  rw [N.end_neck_connection] at hcompare
  have hcompareA : N.connection.scalarCurvature x ≤
      A * N.connection.scalarCurvature N.end_neck.center :=
    hcompare.trans (mul_le_mul_of_nonneg_right (hC.trans (le_max_right _ _)) hRend.le)
  have hHA := hscalar.trans hcompareA
  have herror : H / (4 * A) ≤ N.connection.scalarCurvature N.end_neck.center / 4 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * A) (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith only [hHA]
  have htargetEnd : (3 / 4 : ℝ) * N.connection.scalarCurvature N.end_neck.center ≤
      D.scalarCurvature (f N.end_neck.center) := by
    have hlo := (abs_le.mp (henderror.trans herror)).1
    linarith only [hlo]
  refine ⟨(mul_pos (by norm_num) hRend).trans_le htargetEnd, ?_⟩
  have htargetX : D.scalarCurvature (f x) ≤
      A * N.connection.scalarCurvature N.end_neck.center +
        N.connection.scalarCurvature N.end_neck.center / 4 := by
    have hhi := (abs_le.mp (hxerror.trans herror)).2
    linarith only [hhi, hcompareA]
  have hAR : N.connection.scalarCurvature N.end_neck.center ≤
      A * N.connection.scalarCurvature N.end_neck.center := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA1 hRend.le
  have htarget := mul_le_mul_of_nonneg_left htargetEnd (by positivity : 0 ≤ 4 * A)
  change D.scalarCurvature (f x) ≤ (4 * A) * D.scalarCurvature (f N.end_neck.center)
  nlinarith only [htargetX, hAR, htarget, hRend.le]

end PoincareConjecture.M47
