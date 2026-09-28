import PoincareConjecture.Proofs.M15.Lemma8_7_SquareRootLift
import PoincareConjecture.Proofs.M15.Lemma8_6_HorizontalSpeed
import PoincareConjecture.Proofs.M15.Prop8_2_LocalEstimates

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M15

theorem exists_actualBallCylinder_lift_terminal_speed_bound
    (hM04 : RicciFlowCurvatureTheory.{u}) (n : ℕ)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} n) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (X : Type u) [TopologicalSpace X] (time : X → ℝ)
        (I : SpacetimeInterval) (G : GeneralizedLGeometryTransport n X time I)
        (T : ℝ) (x : (G.slices T).Point) (r : ℝ) (K : SpacetimeInterval)
        (C : Type u) [TopologicalSpace C]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
        [T2Space C] [SecondCountableTopology C]
        (B : M15ActualBallCylinder G T x r K C),
        IsCompact (closure ((G.slices T).metricOnPoints.ball x r)) →
        ∀ (_D : SpacetimeHorizontalConnection G.leafwise)
          (tau : ℝ) (y : G.Point) (p : M14BackwardPath G T 0 tau x.val y)
          (R : M14SquareRootPath G p)
          (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval 0 tau)
            R.horizontal_velocity)
          (S : ℝ), 0 < S → S ≤ Real.sqrt tau → S ^ 2 ≤ r ^ 2 / 2 →
          (∀ s ∈ Set.Ioo 0 S,
            M14SquareRootEulerResidual G R E s (R.horizontal_velocity s) = 0) →
          ∀ L : ℝ → (G.timeIntervals.interval K).Point × C,
          (∀ s ∈ Set.Icc 0 S, B.embedding.toSpacetime (L s) = R.curve s) →
          (∀ s ∈ Set.Icc 0 S,
            B.source_map (L s).2 ∈ (G.slices T).metricOnPoints.ball x (r / 2)) →
          ∀ s ∈ Set.Icc 0 S,
            (B.metric.metric T).tangentNorm (L s).2
              (mfderivWithin 𝓘(ℝ) (𝓡 n) (fun t => (L t).2) (Set.Icc 0 S) s 1) ≤
            Real.exp (2 * (n : ℝ) * (r⁻¹) ^ 2 * s ^ 2) *
              (Real.sqrt (G.spacetime.horizontalMetric.inner (R.curve 0)
                (R.horizontal_velocity 0) (R.horizontal_velocity 0)) +
                (2 / 3 : ℝ) * (A / r ^ 3) * s ^ 3) := by
  obtain ⟨A, hA, hgrad⟩ :=
    exists_actualBallCylinder_horizontal_scalar_gradient_bound hM04 n hM12 hM13
  refine ⟨A, hA, ?_⟩
  intro X _ time I G T x r K C _ _ _ _ _ B hcompact D tau y p R E S hS hStau
    hSr hEuler L hL hhalf s hs
  have hr := B.radius_pos
  have hsub : Icc 0 S ⊆ M14SqrtParameterInterval 0 tau := by
    intro t ht
    exact ⟨by simpa only [Real.sqrt_zero] using ht.1, ht.2.trans hStau⟩
  have hclock (t : ℝ) (ht : t ∈ Icc 0 S) : (L t).1.val = T - t ^ 2 := by
    have h := B.embedding.time_eq (L t)
    rw [hL t ht, R.curve_time t (hsub ht)] at h
    exact h.symm
  have hlast (t : ℝ) (ht : t ∈ Icc 0 S) : T - r ^ 2 / 2 ≤ (L t).1.val := by
    rw [hclock t ht]
    have htS := pow_le_pow_left₀ ht.1 ht.2 2
    linarith
  have hRicci (t : ℝ) (ht : t ∈ Ioo 0 S) :
      |horizontalRicci G.leafwise (R.curve t)
        (R.horizontal_velocity t) (R.horizontal_velocity t)| ≤
      ((n : ℝ) * (r⁻¹) ^ 2) * G.spacetime.horizontalMetric.inner (R.curve t)
        (R.horizontal_velocity t) (R.horizontal_velocity t) := by
    have hRm := B.curvature_bound (L t).1 (L t).2
    change horizontalCurvatureNorm G.leafwise (B.embedding.toSpacetime (L t)) ≤ _ at hRm
    rw [hL t ⟨ht.1.le, ht.2.le⟩] at hRm
    have hq : 0 ≤ G.spacetime.horizontalMetric.inner (R.curve t)
        (R.horizontal_velocity t) (R.horizontal_velocity t) := by
      by_cases hz : R.horizontal_velocity t = 0
      · simp [hz]
      · exact (G.spacetime.horizontalMetric.pos _ _ hz).le
    exact (abs_horizontalRicci_le_curvatureNorm (R.curve t) (R.horizontal_velocity t)).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRm (Nat.cast_nonneg n)) hq)
  have hScalar (t : ℝ) (ht : t ∈ Ioo 0 S) :
      |M14HorizontalScalarDifferential G (R.curve t) (R.horizontal_velocity t).val| ≤
      (A / r ^ 3) * Real.sqrt (G.spacetime.horizontalMetric.inner (R.curve t)
        (R.horizontal_velocity t) (R.horizontal_velocity t)) := by
    have ht' : t ∈ Icc 0 S := ⟨ht.1.le, ht.2.le⟩
    have hg := hgrad X time I G T x r K C B hcompact (L t).1
      (hlast t ht') (L t).2 (hhalf t ht')
    change ∀ w : G.Horizontal (B.embedding.toSpacetime (L t)),
      |M14HorizontalScalarDifferential G (B.embedding.toSpacetime (L t)) w.val| ≤
        (A / r ^ 3) * Real.sqrt
          (G.spacetime.horizontalMetric.inner (B.embedding.toSpacetime (L t)) w w) at hg
    rw [hL t ht'] at hg
    exact hg (R.horizontal_velocity t)
  have hspeed := squareRootPath_speed_le D R E hS.le hStau
    (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg r⁻¹))
    (div_nonneg hA.le (pow_nonneg hr.le 3)) hEuler hRicci hScalar s hs
  obtain ⟨F, hmetric, hRm, _⟩ := actualBallCylinder_exists_flow hM12 B
  let v := mfderivWithin 𝓘(ℝ) (𝓡 n) (fun t => (L t).2) (Icc 0 S) s 1
  have hcurv : ∀ t ∈ Icc (L s).1.val T,
      (F.connection t).curvatureTensorNorm (L s).2 ≤ (r⁻¹) ^ 2 := by
    intro t ht
    have htK := F.interval.out (L s).1.property B.base_mem ht
    rw [hRm ⟨t, htK⟩ (L s).2]
    exact B.curvature_bound ⟨t, htK⟩ (L s).2
  have htime : (L s).1.val ≤ T := by
    rw [hclock s hs]
    linarith [sq_nonneg s]
  have hcompare := (M04.tangentNorm_comparison_at_of_curvature_bound F
    (L s).1.property B.base_mem htime (sq_nonneg r⁻¹) (L s).2 hcurv v).2
  rw [hmetric] at hcompare
  have heq := squareRootPath_lift_speed_eq G (G.timeIntervals.interval K)
    B.embedding B.metric R hS hStau L hL s hs
  change (B.metric.metric (L s).1.val).tangentNorm (L s).2 v = _ at heq
  rw [heq] at hcompare
  apply (hcompare.trans (mul_le_mul_of_nonneg_left hspeed (Real.exp_pos _).le)).trans_eq
  rw [← mul_assoc, ← Real.exp_add, hclock s hs]
  congr 2
  ring

end PoincareConjecture.Proofs.M15
