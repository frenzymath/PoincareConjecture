import PoincareLib.Geometry.Riemannian.Comparison.Volume.Nonnegative
import PoincareLib.Geometry.RicciFlow.Restriction
import PoincareLib.Geometry.Curvature.Operator.NormBounds
import PoincareLib.Geometry.Curvature.Operator.SectionalBounds
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.ScalarIntegral

/-!
# Initial volume bounds on fixed connected components

The complete initial slice has a positive unit-ball volume bound on each
fixed connected component when its curvature operator is nonnegative and
bounded. The supplied M04 theory converts the operator bound to a tensor
bound; the geometric volume theorem then applies to the restricted component.

The short-time corollary additionally uses the scalar-integral parent through
its linear volume-loss estimate. That corollary retains the parent's visible
Petrunin admission. The initial-slice theorem does not use that parent.

References: Maeder--Baumdicker--Seidel, Theorem 1 and Remark 1.1, p. 4;
Cabezas-Rivas--Wilking, Proposition 4.3 and Corollary 4.4, p. 3161.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareMT.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

/-- A bounded nonnegative initial curvature operator gives a positive uniform
unit-ball volume bound on a fixed connected component. Only the supplied M04
tensor-calculus field is used beyond the proved geometric volume theorem. -/
theorem exists_initial_unit_ball_volume_lower_bound_on_component
    (hM04 : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J) (hn : 1 ≤ n)
    (p : M) (a : ℝ) (hcomplete : MetricComplete (F.metric a))
    (hoperator : ∀ x ∈ connectedComponent p,
      (F.connection a).NonnegativeCurvatureOperator x)
    (hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ connectedComponent p,
      (F.connection a).CurvatureOperatorBound K x) :
    ∃ v : ℝ, 0 < v ∧ ∀ x ∈ connectedComponent p,
      ENNReal.ofReal v ≤ (F.metric a).volumeMeasure ((F.metric a).ball x 1) := by
  obtain ⟨K, hK, hb⟩ := hbound
  let G := F.restrictComponent p
  have hcurv (x : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p) :
      (G.connection a).curvatureTensorNorm x ≤ (n : ℝ) ^ 2 * K := by
    rw [F.restrictComponent_curvatureTensorNorm]
    exact (F.connection a).curvatureTensorNorm_le_of_operator_bound x K hK
      (hb x x.property) (hM04.tensor_calculus n M (F.metric a) (F.connection a))
  obtain ⟨v, hv, hvolume⟩ := (G.metric a).exists_uniform_unit_ball_volume_lower_bound
    (G.connection a) hn (F.restrictComponent_metricComplete p a hcomplete)
    (mul_nonneg (sq_nonneg (n : ℝ)) hK) (by
      intro x u w
      refine ⟨(G.connection a).sectionalCurvature_nonneg_of_nonnegative_curvatureOperator
        x ((F.restrictComponent_nonnegativeCurvatureOperator_iff p a x).mpr
          (hoperator x x.property)) u w, ?_⟩
      exact (le_abs_self _).trans
        (((G.connection a).abs_sectionalCurvature_le_curvatureTensorNorm x u w).trans
          (hcurv x)))
  refine ⟨v, hv, ?_⟩
  intro x hx
  have h := hvolume ⟨x, hx⟩
  rwa [F.restrictComponent_volumeMeasure_ball] at h

/-- The existing scalar-integral volume-loss theorem preserves a positive
componentwise volume bound for a short right interval. This corollary depends
on Petrunin's still-admitted scalar-integral theorem through
`exists_uniform_unitBall_volume_lower_bound`; it is not an independent proof
of that estimate. -/
theorem exists_right_unit_ball_volume_lower_bound_on_component
    (hM04 : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J) (hn : 1 ≤ n)
    (p : M) {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Icc a b, ∀ x ∈ connectedComponent p,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ connectedComponent p,
      (F.connection a).CurvatureOperatorBound K x) :
    ∃ d ∈ Ioc a b, ∃ v : ℝ, 0 < v ∧ ∀ t ∈ Icc a d,
      ∀ x ∈ connectedComponent p,
        ENNReal.ofReal v ≤ (F.metric t).volumeMeasure ((F.metric t).ball x 1) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  obtain ⟨v, hv, hvolume⟩ := F.exists_initial_unit_ball_volume_lower_bound_on_component
    hM04 hn p a (hcomplete a ha) (hoperator a ha) hbound
  obtain ⟨P, hP, hloss⟩ := exists_uniform_unitBall_volume_lower_bound.{u} n
  let δ := min (b - a) (v / (2 * P))
  have hδ : 0 < δ := lt_min (sub_pos.mpr hab) (div_pos hv (by positivity))
  have hδb : δ ≤ b - a := min_le_left _ _
  have hδv : P * δ ≤ v / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * P)).mp (min_le_right (b - a) (v / (2 * P)))
    change δ * (2 * P) ≤ v at h
    nlinarith
  refine ⟨a + δ, ⟨by linarith, by linarith⟩, v / 2, half_pos hv, ?_⟩
  intro t ht x hx
  have ht' : t ∈ Icc a b := ⟨ht.1, ht.2.trans (by linarith)⟩
  let G := F.restrictComponent p
  let x' : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p := ⟨x, hx⟩
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht'.2
  have hl := hloss _ J G a t ht.1 (hsub.trans hJ)
    (fun s _ => hM04.tensor_calculus n _ (G.metric s) (G.connection s))
    (fun s hs => F.restrictComponent_metricComplete p s (hcomplete s (hsub hs)))
    (fun s hs y => (F.restrictComponent_nonnegativeCurvatureOperator_iff p s y).mpr
      (hoperator s (hsub hs) y y.property)) x'
  simp only [G, F.restrictComponent_volumeMeasure_ball] at hl
  have hfinite : (F.metric a).volumeMeasure ((F.metric a).ball x 1) ≠ ⊤ := by
    have hsubball : (F.metric a).ball x 1 ⊆ {y | (F.metric a).edist x y ≤ ENNReal.ofReal 1} :=
      fun y hy => (show (F.metric a).edist x y < ENNReal.ofReal 1 from hy).le
    exact (lt_of_le_of_lt (measure_mono hsubball)
      ((F.metric a).volumeMeasure_lt_top_of_isCompact
        ((F.metric a).isCompact_closedBall_of_metricComplete (hcomplete a ha) x 1))).ne
  have hvreal : v ≤ ((F.metric a).volumeMeasure ((F.metric a).ball x 1)).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hfinite).mp (hvolume x hx)
  have htime : P * (t - a) ≤ v / 2 :=
    (mul_le_mul_of_nonneg_left (by linarith [ht.2] : t - a ≤ δ) hP.le).trans hδv
  apply ENNReal.ofReal_le_of_le_toReal
  change v / 2 ≤ ((F.metric t).volumeMeasure ((F.metric t).ball x 1)).toReal
  change ((F.metric a).volumeMeasure ((F.metric a).ball x 1)).toReal - P * (t - a) ≤
    ((F.metric t).volumeMeasure ((F.metric t).ball x 1)).toReal at hl
  linarith

end PoincareMT.RicciFlow
