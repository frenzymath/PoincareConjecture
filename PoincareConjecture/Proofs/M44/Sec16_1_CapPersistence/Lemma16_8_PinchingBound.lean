import PoincareConjecture.Statements.M44Providers
import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Curvature.ThreeDimensional
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.Bounds

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem SurgeryPinchedOn.curvature_norm_le
    (P : M44CapPersistencePredecessors.{u}) {g : RiemannianMetric 3 M}
    {D : LeviCivitaData g} {t : ℝ} {U : Set M}
    (hpinch : SurgeryPinchedOn D t U) {x : M} (hx : x ∈ U) :
    D.curvatureTensorNorm x ≤ 13 * max (D.scalarCurvature x) (Real.exp 4) := by
  obtain ⟨k1, k2, k3, h12, h23, hleast, hscalar, hnorm⟩ :=
    D.three_dimensional_curvature_spectrum (P.curvature.tensor_calculus 3 M g D) x
  have hlog : 0 < max (-k3) 0 →
      2 * max (-k3) 0 * (Real.log (max (-k3) 0) + Real.log (1 + t) - 3) ≤
        D.scalarCurvature x := by
    intro hX
    have hX' : 0 < D.negativeCurvaturePart x := by
      simpa only [LeviCivitaData.negativeCurvaturePart, hleast] using hX
    simpa only [LeviCivitaData.negativeCurvaturePart, hleast] using hpinch.2.2 x hx hX'
  exact Poincare.fullNorm_le_of_hamiltonIvey hpinch.1 h12 h23 hscalar hnorm le_rfl hlog

theorem SurgeryPinchedOn.scaled_curvature_norm_le
    (P : M44CapPersistencePredecessors.{u}) {g : RiemannianMetric 3 M}
    {D : LeviCivitaData g} {t : ℝ} {U : Set M}
    (hpinch : SurgeryPinchedOn D t U) {x : M} (hx : x ∈ U)
    {scale B : ℝ} (hscale : 0 ≤ scale) (hsmall : scale ≤ 1)
    (hscalar : scale * D.scalarCurvature x ≤ B) :
    scale * D.curvatureTensorNorm x ≤ 13 * max B (Real.exp 4) := by
  calc
    scale * D.curvatureTensorNorm x ≤
        scale * (13 * max (D.scalarCurvature x) (Real.exp 4)) :=
      mul_le_mul_of_nonneg_left (hpinch.curvature_norm_le P hx) hscale
    _ = 13 * max (scale * D.scalarCurvature x) (scale * Real.exp 4) := by
      rw [← mul_max_of_nonneg _ _ hscale]
      ring
    _ ≤ 13 * max B (Real.exp 4) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact max_le_max hscalar (by nlinarith [Real.exp_pos (4 : ℝ)])

theorem SurgeryFlowPinched.cap_curvature_norm_le
    {F : SurgeryFlowData.{u}} (hpinch : SurgeryFlowPinched F)
    (P : M44CapPersistencePredecessors.{u}) {t h B : ℝ}
    (ht : t ∈ F.time_domain) (hh : h ^ 2 ≤ 1)
    (x : (F.slice t).carrier)
    (hscalar : h ^ 2 * (F.connection t).scalarCurvature x ≤ B) :
    h ^ 2 * (F.connection t).curvatureTensorNorm x ≤ 13 * max B (Real.exp 4) :=
  (hpinch t ht).scaled_curvature_norm_le P (Set.mem_univ x) (sq_nonneg h) hh hscalar

end PoincareConjecture
