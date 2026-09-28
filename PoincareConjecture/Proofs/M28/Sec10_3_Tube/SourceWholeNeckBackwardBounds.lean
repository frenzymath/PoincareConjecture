import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceWholeNeckBackwardPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 1600000 in

theorem exists_whole_neck_backward_bounds_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
      ∃ K : ℝ, 0 < K ∧
        ∀ {epsilon C A : ℝ}
          {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
            ((n : ℝ) + 1) ((n : ℝ) + 1)}
          (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H),
          epsilon ≤ epsilon0 →
          ∀ (G : RegularPointedMetricConvergence
            (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
            (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
            letI := G.limitCarrier.topologicalSpace
            letI := G.limitCarrier.chartedSpace
            letI := G.limitCarrier.isManifold
            ∀ (sigma : ℕ → ℕ) (V : EpsilonNeck G.limitMetric)
              (D : WholeNeckBackwardData H W G sigma V),
              (∀ k s, s ∈ Icc (-(V.scale ^ 2 / 2)) 0 →
                ∀ x : strongNeckOpen (D.neck k),
                  ((D.sourceFlow k).connection s).curvatureTensorNorm x ≤
                    2 * K / V.scale ^ 2) ∧
              (∀ k s, s ∈ Icc (-(V.scale ^ 2 / 2)) 0 →
                ∀ x : D.fixedDomain,
                  ((D.fixedFlow k).connection s).curvatureTensorNorm x ≤
                    2 * K / V.scale ^ 2) ∧
              ∀ m : ℕ, ∃ B : ℝ, 0 < B ∧
                ∀ k s, s ∈ Icc (-(V.scale ^ 2 / 2)) 0 →
                  ∀ x : D.fixedDomain,
                    ((D.fixedFlow k).connection s).curvatureDerivativeNorm m x ≤ B := by
  obtain ⟨epsilon0, hpos, hsmall, K, hK, hsource⟩ :=
    exists_strongNeck_buffered_global_bounds_accuracy P.local_derivative_estimates
  refine ⟨epsilon0, hpos, hsmall, K, hK, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro sigma V D
  have ha : 0 < V.scale ^ 2 := sq_pos_of_pos V.scale_pos
  obtain ⟨B, hB, hbounds⟩ := hsource epsilon D.epsilon_pos hepsilon
  have hfloor (k : ℕ) : V.scale ^ 2 / 2 ≤
      D.normalization k * (D.neck k).scale ^ 2 := by
    have hlower := D.scale_lower k
    change (4 / 5 : ℝ) * V.scale ^ 2 ≤
      D.normalization k * (D.neck k).scale ^ 2 at hlower
    linarith only [hlower, ha]
  have hbound (k : ℕ) := hbounds
    (E (D.sourceIndex k + H.shift)).flow
    (E (D.sourceIndex k + H.shift)).time (D.neck k) (D.raw k)
    (D.normalization k) (D.normalization_pos k)
    (V.scale ^ 2 / 2) (half_pos ha) (hfloor k)
    (V.scale ^ 2 / 2) (half_pos ha) (D.half_window k)
  have hcurv : ∀ k s, s ∈ Icc (-(V.scale ^ 2 / 2)) 0 →
      ∀ x : strongNeckOpen (D.neck k),
        ((D.sourceFlow k).connection s).curvatureTensorNorm x ≤
          2 * K / V.scale ^ 2 := by
    intro k s hs x
    have h := (hbound k).1 s hs x
    change ((D.sourceFlow k).connection s).curvatureTensorNorm x ≤
      K / (V.scale ^ 2 / 2) at h
    simpa only [div_div_eq_mul_div, mul_comm K 2] using h
  refine ⟨hcurv, ?_, ?_⟩
  · intro k s hs x
    rw [D.fixedFlow_curvatureTensorNorm]
    exact hcurv k s hs (D.neckMap k x)
  · intro m
    refine ⟨(Real.sqrt (V.scale ^ 2 / 2))⁻¹ ^ (m + 2) * B m, ?_, ?_⟩
    · exact mul_pos
        (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (half_pos ha))) _) (hB m)
    intro k s hs x
    rw [D.fixedFlow_curvatureDerivativeNorm]
    exact (hbound k).2 m s hs (D.neckMap k x) (D.originalMap_in_core k x).2.le

end PoincareConjecture.M28.CounterexampleNeckFamily
