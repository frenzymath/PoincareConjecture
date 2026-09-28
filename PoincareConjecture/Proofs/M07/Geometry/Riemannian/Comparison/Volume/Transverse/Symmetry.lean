import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Transverse.CurvatureTrace
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Variation.Manifold

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

open Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture

private theorem christoffelCurvature_cyclic_of_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {x : E}
    (hΓ : DifferentiableAt ℝ Γ x)
    (hs : ∀ᶠ y in 𝓝 x, ∀ u v, Γ y u v = Γ y v u) (u v w : E) :
    ConnectionVariation.christoffelCurvature Γ x u v w +
      ConnectionVariation.christoffelCurvature Γ x v w u +
      ConnectionVariation.christoffelCurvature Γ x w u v = 0 := by
  have hd (a b c : E) : fderiv ℝ Γ x a b c = fderiv ℝ Γ x a c b := by
    have hbc := (hΓ.hasFDerivAt.clm_apply (hasFDerivAt_const b x)).clm_apply
      (hasFDerivAt_const c x)
    have hcb := (hΓ.hasFDerivAt.clm_apply (hasFDerivAt_const c x)).clm_apply
      (hasFDerivAt_const b x)
    have heq : (fun y => Γ y b c) =ᶠ[𝓝 x] (fun y => Γ y c b) :=
      hs.mono fun y hy => hy b c
    have he := congrArg (fun A : E →L[ℝ] E => A a)
      (hbc.fderiv.symm.trans (heq.fderiv_eq.trans hcb.fderiv))
    simpa only [add_apply, ContinuousLinearMap.comp_apply, zero_apply, map_zero,
      ContinuousLinearMap.flip_apply, zero_add] using he
  have hsx := hs.self_of_nhds
  simp only [ConnectionVariation.christoffelCurvature]
  rw [hd v u w, hd w v u, hd u w v, hsx v w, hsx u w, hsx v u]
  abel

namespace LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem curvature_cyclic_eq_zero
    (D : LeviCivitaData g) (x : M) (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x u v w + D.curvature x v w u + D.curvature x w u v = 0 := by
  let c := extChartAt (𝓡 n) x
  let B := g.pullbackCoefficients c.symm
  let L := mfderiv (𝓡 n) (𝓡 n) c x
  have hx : x ∈ c.source := mem_extChartAt_source x
  have hcx : c x ∈ c.target := c.map_source hx
  have hB := (g.contDiffOn_chartCoefficients x).contDiffAt
    ((isOpen_extChartAt_target x).mem_nhds hcx)
  have hΓ := (CoordinateExponential.contDiffAt_christoffelBilinear hB
    (g.isInvertible_chartCoefficients x hcx)).differentiableAt (by simp)
  have hs : ∀ᶠ y in 𝓝 (c x), ∀ a b,
      CoordinateExponential.christoffelBilinear B y a b =
        CoordinateExponential.christoffelBilinear B y b a := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hcx] with y hy
    apply CoordinateExponential.christoffelBilinear_symm
      (((g.contDiffOn_chartCoefficients x).contDiffAt
        ((isOpen_extChartAt_target x).mem_nhds hy)).differentiableAt (by simp))
    exact Filter.Eventually.of_forall fun z a b => g.symm _ _ _
  have hc := christoffelCurvature_cyclic_of_symm hΓ hs (L u) (L v) (L w)
  simp only [← CoordinateExponential.coordinateCurvature_eq_christoffelCurvature hΓ] at hc
  apply (isInvertible_mfderiv_extChartAt hx).injective
  change L (D.curvature x u v w + D.curvature x v w u + D.curvature x w u v) = L 0
  rw [map_add, map_add, map_zero]
  simpa only [L, B, c, ConnectionVariation.coordinateCurvature_in_chart g D x hx] using hc

theorem inner_radial_curvature_symm
    (D : LeviCivitaData g) (x : M) (u v w : TangentSpace (𝓡 n) x) :
    g.inner x (D.curvature x u v v) w = g.inner x u (D.curvature x w v v) := by
  have h := congrArg (fun z => g.inner x z v) (D.curvature_cyclic_eq_zero x u v w)
  simp only [map_add, add_apply, map_zero, zero_apply] at h
  change D.curvatureTensor x u v v w + D.curvatureTensor x v w v u +
    D.curvatureTensor x w u v v = 0 at h
  rw [D.curvatureTensor_swap_last x u v v w,
    D.curvatureTensor_swap_first x v w v u,
    D.curvatureTensor_swap_last x w v v u,
    D.curvatureTensor_zero_last x w u v] at h
  rw [g.symm x u (D.curvature x w v v)]
  change D.curvatureTensor x u v w v = D.curvatureTensor x w v u v
  linarith

end LeviCivitaData

end PoincareConjecture
