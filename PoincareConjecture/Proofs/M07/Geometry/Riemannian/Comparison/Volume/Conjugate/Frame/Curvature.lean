import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Frame.Coefficient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.ConjugateFrame

open ConnectionAlongCurve ConnectionVariation CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem coordinateCurvature_cyclic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hsym : ∀ᶠ y in 𝓝 x, ∀ u v, coordinateChristoffel B y u v =
      coordinateChristoffel B y v u) (u v w : E) :
    coordinateCurvature B x u v w + coordinateCurvature B x v w u +
      coordinateCurvature B x w u v = 0 := by
  have hder (a b : E) : fderiv ℝ (fun y => coordinateChristoffel B y a b) x =
      fderiv ℝ (fun y => coordinateChristoffel B y b a) x :=
    Filter.EventuallyEq.fderiv_eq (hsym.mono fun _ hy => hy a b)
  have hs := hsym.self_of_nhds
  unfold coordinateCurvature
  rw [hder w u, hder w v, hder v u, hs w u, hs w v, hs v u]
  abel

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem curvature_cyclic (D : LeviCivitaData g) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    D.curvature x u v w + D.curvature x v w u + D.curvature x w u v = 0 := by
  let c := extChartAt (𝓡 n) x
  let B := g.pullbackCoefficients c.symm
  have hx : x ∈ c.source := mem_extChartAt_source x
  have hc : c x ∈ c.target := c.map_source hx
  have hs : ∀ᶠ y in 𝓝 (c x), ∀ a b, coordinateChristoffel B y a b =
      coordinateChristoffel B y b a := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds hc] with y hy a b
    exact christoffelBilinear_symm
      (((g.contDiffOn_chartCoefficients x).contDiffAt
        ((isOpen_extChartAt_target x).mem_nhds hy)).differentiableAt (by simp))
      (Filter.Eventually.of_forall fun z a b => g.symm _ _ _) a b
  apply (isInvertible_mfderiv_extChartAt hx).injective
  simp only [map_add, map_zero]
  rw [← coordinateCurvature_in_chart g D x hx,
    ← coordinateCurvature_in_chart g D x hx,
    ← coordinateCurvature_in_chart g D x hx]
  exact coordinateCurvature_cyclic hs _ _ _

theorem curvature_jacobi_symm (D : LeviCivitaData g) (x : M)
    (u v T : TangentSpace (𝓡 n) x) :
    g.inner x (D.curvature x u T T) v = g.inner x u (D.curvature x v T T) := by
  have h := congrArg (fun z => g.inner x z T) (curvature_cyclic D x u T v)
  have h₁ := D.curvatureTensor_swap_last x u T T v
  have h₂ := D.curvatureTensor_swap_last x T v T u
  have h₃ := D.curvatureTensor_swap_first x T v u T
  have hz := D.curvatureTensor_zero_last x v u T
  change g.inner x (D.curvature x u T v) T =
    -g.inner x (D.curvature x u T T) v at h₁
  change g.inner x (D.curvature x T v u) T =
    -g.inner x (D.curvature x T v T) u at h₂
  change g.inner x (D.curvature x T v T) u =
    -g.inner x (D.curvature x v T T) u at h₃
  change g.inner x (D.curvature x v u T) T = 0 at hz
  simp only [map_add, map_zero, add_apply, zero_apply] at h
  rw [g.symm x u (D.curvature x v T T)]
  linarith

theorem coefficient_metric_symm (D : LeviCivitaData g)
    {q : ℝ → M} {P : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {a t : ℝ} (hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q t)
    (hi : (P t).IsInvertible)
    (hp : ∀ u v, g.inner (q t) (P t u) (P t v) = g.inner (q a) u v)
    (u v : EuclideanSpace ℝ (Fin n)) :
    g.inner (q a) (coefficient g q P t u) v =
      g.inner (q a) u (coefficient g q P t v) := by
  simp only [coefficient, chartCoefficient_apply D P (mem_extChartAt_source _) hq]
  rw [← hp, ← hp, hi.self_apply_inverse, hi.self_apply_inverse]
  exact curvature_jacobi_symm D _ _ _ _

end PoincareConjecture.ConjugateFrame
