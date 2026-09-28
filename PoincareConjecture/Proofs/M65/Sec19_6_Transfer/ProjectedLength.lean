import PoincareConjecture.Proofs.M58.Sec18_4_LoopLength
import PoincareConjecture.Proofs.M62.Lemma0_4_Continuity
import PoincareConjecture.Definitions.M63Family

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}

theorem m65Projection_tangentNorm_le (P : M62.CircleProductData F circumference)
    (t : ℝ) (q : P.charts.Point) (v : TangentSpace (𝓡 (n + 1)) q) :
    (F.metric t).tangentNorm q.1 (P.charts.split q v).1 ≤
      (P.flow.metric t).tangentNorm q v := by
  unfold RiemannianMetric.tangentNorm
  apply Real.sqrt_le_sqrt
  rw [P.metric_eq]
  exact le_add_of_nonneg_right
    ((P.circle.metricOnPoints.toRiemannianMetric.toCore q.2).re_inner_nonneg _)

theorem m65Projection_speed_le (P : M62.CircleProductData F circumference)
    (gamma : ℝ → P.charts.Point) {x : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)) gamma x) (t : ℝ) :
    (F.metric t).tangentNorm (gamma x).1
        (curveVelocity (fun y => (gamma y).1) x) ≤
      (P.flow.metric t).tangentNorm (gamma x) (curveVelocity gamma x) := by
  let := P.charts.chartedSpace
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have hchain := mfderiv_comp_apply (f := gamma) (g := (Prod.fst : P.charts.Point → M))
    x (hfst.mdifferentiableAt (by simp)) hgamma (1 : ℝ)
  change curveVelocity (fun y => (gamma y).1) x =
    mfderiv (𝓡 (n + 1)) (𝓡 n) (Prod.fst : P.charts.Point → M)
      (gamma x) (curveVelocity gamma x) at hchain
  rw [← P.charts.split_space] at hchain
  rw [hchain]
  exact m65Projection_tangentNorm_le P t (gamma x) (curveVelocity gamma x)

theorem m65ProjectedFamilyLength_le
    {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {a b : ℝ} {F : RicciFlow 3 M (Set.Icc a b)}
    {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))}
    {zeta circumference : ℝ} {P : M62.CircleProductData F circumference}
    {approximation : M63RawApproximation F Gamma zeta}
    (S : M63ProductSolutionFamily P approximation) (t : Set.Icc a b) (z : LoopTwoSphere) :
    freeLoopLength (F.metric t) (S.projected t z) ≤ m62Length P.flow (S.curve z) t := by
  unfold freeLoopLength m62Length
  apply intervalIntegral.integral_mono_on (by unfold curvePeriod; positivity)
    ((Proofs.M58.continuous_freeLoopSpeed (F.metric t) (S.projected t z)).intervalIntegrable _ _)
    (M62.length_integrable P.flow (S.curve z) (S.shrinking z) t.2)
  intro x _
  rw [funext (S.projected_eq t z)]
  exact m65Projection_speed_le P (fun y => S.curve z y t)
    ((S.shrinking z).spatial_regular t t.2 |>.mdifferentiableAt (by simp)) t

end PoincareConjecture
