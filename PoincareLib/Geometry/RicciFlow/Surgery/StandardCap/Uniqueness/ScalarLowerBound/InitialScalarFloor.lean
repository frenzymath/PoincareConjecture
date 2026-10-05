import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.ExistenceData
import PoincareLib.Geometry.RicciFlow.Harnack.Matrix.Bounds
import PoincareLib.Geometry.RicciFlow.Harnack.Regularity
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Calculus.RiemannianProper
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.RawFlow.MetricSpace
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A positive scalar floor on an initial strip

Morgan-Tian, Proposition 12.31, pp. 325-326, using Lemma 12.3 and the
initial derivative estimates of Chapter 4. The selected initial connection
and the spatially uniform Shi estimate give a uniform lower time derivative
for scalar curvature. See `derivations/05-positive-scalar-floor.md`.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareMT.RepairedStandardCapExistenceData

/-- Proposition 12.31, pp. 325-326: initial derivative estimates give one bound
for the actual second curvature derivative everywhere on the first half-strip. -/
theorem exists_initial_second_curvature_bound
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (0 : ℝ) (1 / 2), ∀ x : StandardCapSpace,
      (E.flow.connection t).curvatureDerivativeNorm 2 x ≤ C := by
  classical
  have hhalf : (1 / 2 : ℝ) < E.flow.base.lifetime := by rw [E.lifetime_one]; norm_num
  have hsub : Icc (0 : ℝ) (1 / 2) ⊆ Ico 0 E.flow.base.lifetime :=
    fun _ ht => ⟨ht.1, ht.2.trans_lt hhalf⟩
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow E.flow.base.flow
    hsub (ordConnected_Icc) ⟨0, by norm_num, 1 / 2, by norm_num, by norm_num⟩
  obtain ⟨K₀, hK₀, hcurv⟩ := E.flow.base.curvature_locally_bounded
    (1 / 2) (by norm_num) hhalf
  choose C hC hCb using E.initial_estimate.curvature_derivative_bounds
  let K := max K₀ (∑ j ∈ Finset.range 3, C j) + 1
  have hK₀K : K₀ ≤ K := by dsimp [K]; linarith [le_max_left K₀ (∑ j ∈ Finset.range 3, C j)]
  have hK : 0 < K := by
    dsimp [K]
    linarith [le_max_left K₀ (∑ j ∈ Finset.range 3, C j)]
  have hCK (j : ℕ) (hj : j ≤ 2) : C j ≤ K := by
    have hjmem : j ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
    have hsum := Finset.single_le_sum (fun i (_ : i ∈ Finset.range 3) => hC i) hjmem
    dsimp [K]
    linarith [le_max_right K₀ (∑ j ∈ Finset.range 3, C j)]
  have hinit (j : ℕ) (hj : j ≤ 2) (x : StandardCapSpace) :
      (F.connection 0).curvatureDerivativeNorm j x ≤ K := by
    have htransport (g h : RiemannianMetric 3 StandardCapSpace)
        (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h) (hD : HEq D D') :
        D.curvatureDerivativeNorm j x = D'.curvatureDerivativeNorm j x := by
      subst h
      cases eq_of_heq hD
      rfl
    change (E.flow.base.flow.connection 0).curvatureDerivativeNorm j x ≤ K
    rw [htransport _ _ _ _ E.flow.base.initial_metric E.flow.base.initial_connection]
    exact (hCb j x).trans (hCK j hj)
  obtain ⟨B, hB, hShi⟩ := P.initial_derivative_estimates 3 2 2 K (K / 2) 1
    hK (by positivity) (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro t ht x
  have hcompact : IsCompact (closure ((F.metric 0).ball x 1)) :=
    Proofs.M09.isCompact_closure_metric_ball (F.metric 0)
      (E.complete 0 ⟨le_rfl, E.flow.base.lifetime_pos⟩) x 1
  have hx : x ∈ (F.metric 0).ball x (1 / 2) := by
    change (F.metric 0).edist x x < ENNReal.ofReal (1 / 2)
    rw [← RiemannianMetric.toEMetricSpace_edist]
    have hz := @edist_self StandardCapSpace
      (F.metric 0).toEMetricSpace.toPseudoEMetricSpace x
    rw [hz]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  have htime : (1 / 2 : ℝ) ≤ (K / 2) / K := by
    rw [le_div_iff₀ hK]
    linarith
  have hbound := hShi StandardCapSpace (1 / 2) (by norm_num) htime F x hcompact
    (fun s hs y => ((le_abs_self _).trans (hcurv s hs y)).trans hK₀K)
    hinit t ht (Or.inr le_rfl) x hx
  change (F.connection t).curvatureDerivativeNorm 2 x ≤ B
  simpa only [Nat.sub_self, Nat.cast_zero, zero_div, Real.rpow_zero, div_one] using hbound

/-- Proposition 12.31, pp. 325-326: the scalar has a uniformly bounded downward
rate near time zero, using its actual Laplacian and nonnegative Ricci square. -/
theorem exists_initial_scalar_derivative_lower_bound
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) :
    ∃ L : ℝ, 0 < L ∧ ∀ t ∈ Icc (0 : ℝ) (1 / 2), ∀ x : StandardCapSpace,
      -L ≤ (E.flow.connection t).laplacian (E.flow.connection t).scalarCurvature x +
        2 * (E.flow.connection t).ricciNormSq x := by
  obtain ⟨C, hC, hbound⟩ := E.exists_initial_second_curvature_bound P
  refine ⟨27 * C, by positivity, ?_⟩
  intro t ht x
  have hlap := (E.flow.connection t).abs_laplacian_scalar_le_curvatureDerivativeNorm
    (P.tensor_calculus 3 StandardCapSpace _ _) x
  have hRic : 0 ≤ (E.flow.connection t).ricciNormSq x :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  norm_num only [Nat.cast_ofNat, pow_succ, pow_zero] at hlap
  have h := hbound t ht x
  have hneg := (abs_le.mp hlap).1
  nlinarith

/-- Proposition 12.31, pp. 325-326: a single positive initial scalar floor holds
at all spatial points on a nontrivial closed time interval starting at zero. -/
theorem exists_initial_scalar_floor
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) :
    ∃ δ B : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < B ∧
      ∀ t ∈ Icc 0 δ, ∀ x : StandardCapSpace, B ≤ (E.flow.connection t).scalarCurvature x := by
  obtain ⟨L, hL, hbound⟩ := E.exists_initial_scalar_derivative_lower_bound P
  let a := E.initial_estimate.scalar_constant⁻¹
  have ha : 0 < a := inv_pos.mpr E.initial_estimate.scalar_constant_pos
  let δ := min (1 / 2) (a / (2 * L))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδL : L * δ ≤ a / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * L)).mp (min_le_right (1 / 2) (a / (2 * L)))
    dsimp [δ]
    linarith
  refine ⟨δ, a / 2, hδ, hδhalf, by positivity, ?_⟩
  intro t ht x
  have hsub : Icc 0 δ ⊆ Ico 0 E.flow.base.lifetime := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    rw [E.lifetime_one]
    linarith [hs.2]
  have hderiv (s : ℝ) (hs : s ∈ Icc 0 δ) :=
    (P.scalar_evolution 3 StandardCapSpace _ E.flow.base.flow s (hsub hs) x).mono hsub
  have hmono : MonotoneOn
      (fun s => (E.flow.connection s).scalarCurvature x + L * s) (Icc 0 δ) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 δ)
      (fun s hs => ((hderiv s hs).add ((hasDerivWithinAt_id s _).const_mul L)).continuousWithinAt)
      (fun s hs => ((hderiv s (interior_subset hs)).add
        ((hasDerivWithinAt_id s _).const_mul L)).mono interior_subset)
    intro s hs
    have hs' := interior_subset hs
    have h := hbound s ⟨hs'.1, hs'.2.trans hδhalf⟩ x
    change 0 ≤ (E.flow.connection s).laplacian (E.flow.connection s).scalarCurvature x +
      2 * (E.flow.connection s).ricciNormSq x + L * 1
    linarith
  have hinit : a ≤ (E.flow.connection 0).scalarCurvature x := by
    have htransport (g h : RiemannianMetric 3 StandardCapSpace)
        (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h) (hD : HEq D D') :
        D.scalarCurvature x = D'.scalarCurvature x := by
      subst h
      cases eq_of_heq hD
      rfl
    change a ≤ (E.flow.base.flow.connection 0).scalarCurvature x
    rw [htransport _ _ _ _ E.flow.base.initial_metric E.flow.base.initial_connection]
    exact (E.initial_estimate.scalar_bounds x).1
  have h := hmono ⟨le_rfl, hδ.le⟩ ht ht.1
  have hLt := mul_le_mul_of_nonneg_left ht.2 hL.le
  simp only [mul_zero, add_zero] at h
  linarith

end PoincareMT.RepairedStandardCapExistenceData
