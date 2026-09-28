import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CanonicalAnalytics
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Curvature.ThreeDimensional
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.Bounds










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46



noncomputable def seedCurvatureConstant (r : ℝ) : ℝ :=
  13 * max (2 * r⁻¹ ^ 2) (Real.exp 4)



theorem seedCurvatureConstant_pos (r : ℝ) : 0 < seedCurvatureConstant r :=
  mul_pos (by norm_num) ((Real.exp_pos 4).trans_le (le_max_right _ _))



theorem pinched_curvature_norm_le (P : M46Predecessors.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} {D : LeviCivitaData g} {t : ℝ} {U : Set M}
    (hpinch : SurgeryPinchedOn D t U) {x : M} (hx : x ∈ U) :
    D.curvatureTensorNorm x ≤ 13 * max (D.scalarCurvature x) (Real.exp 4) := by
  obtain ⟨k1, k2, k3, h12, h23, hleast, hscalar, hnorm⟩ :=
    D.three_dimensional_curvature_spectrum (P.m04.tensor_calculus 3 M g D) x
  have hlog : 0 < max (-k3) 0 →
      2 * max (-k3) 0 * (Real.log (max (-k3) 0) + Real.log (1 + t) - 3) ≤
        D.scalarCurvature x := by
    intro hX
    have hX' : 0 < D.negativeCurvaturePart x := by
      simpa only [LeviCivitaData.negativeCurvaturePart, hleast] using hX
    simpa only [LeviCivitaData.negativeCurvaturePart, hleast] using hpinch.2.2 x hx hX'
  exact Poincare.fullNorm_le_of_hamiltonIvey hpinch.1 h12 h23 hscalar hnorm le_rfl hlog



theorem seed_curvature_bound (P : M46Predecessors.{u})
    {F : SurgeryFlowData.{u}} {t r : ℝ} (hpinch : SurgeryPinchedAt (F.connection t) t)
    (x : (F.slice t).carrier)
    (hscalar : (F.connection t).scalarCurvature x ≤ 2 * r⁻¹ ^ 2) :
    (F.connection t).curvatureTensorNorm x ≤ seedCurvatureConstant r :=
  (pinched_curvature_norm_le P hpinch (mem_univ x)).trans
    (mul_le_mul_of_nonneg_left (max_le_max_right _ hscalar) (by norm_num))

end PoincareConjecture.Proofs.M46
