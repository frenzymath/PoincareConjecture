import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.TerminalCylinder








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RawAncientSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

variable (C : ℕ → FlowCarrier.{0} 3)
  (F : ∀ k, RicciFlow 3 (C k).carrier (Iic 0)) (p : ∀ k, (C k).carrier)



theorem exists_terminal_cylinderCover_jet_constant
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (radius : ℕ → ℝ) (hradius : Tendsto radius atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (radius k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    {J : Set ℝ} (hJ : IsCompact J) (d : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {δ s : ℝ}, 0 < δ → δ ≤ 1 →
      (1 / 2 : ℝ) ≤ s → s ≤ 1 →
      ∀ G : AncientPointedGeometricConvergence C (fun k t => (F k).metric (t - δ)) p δ,
        G.limitCarrier.metricComplete (G.limitFlow.metric 0) →
      ∀ Φ : RoundCylinderSpace → G.limitCarrier.carrier,
        IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ →
        (fun z v w => s * roundCylinderPullback (G.limitFlow.metric 0) Φ z v w) =
          EvolvingRoundCylinderMetric 0 →
        ∀ᶠ i in atTop, ∀ q : UnitTwoSphere, ∀ r ∈ J, ∀ j ≤ d,
          let e : RoundCylinderCoordinates → (C (G.subsequence i)).carrier :=
            fun y => G.embedding i (Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2))
          ‖iteratedFDeriv ℝ j (((F (G.subsequence i)).metric 0).parametrizedCoefficients e)
              (0, r) -
            iteratedFDeriv ℝ j (((F (G.subsequence i)).metric (-δ)).parametrizedCoefficients e)
              (0, r)‖ ≤ B * δ := by
  let K : Set RoundCylinderCoordinates := {0} ×ˢ J
  have hK : IsCompact K := isCompact_singleton.prod hJ
  have hKU : K ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ := by
    rintro x ⟨hx, _⟩
    exact ⟨by simpa only [mem_singleton_iff.mp hx] using
      (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)), mem_univ _⟩
  obtain ⟨Z, hZ, hinit⟩ :=
    PointedGeometricConvergence.exists_eventual_cylinder_parametrized_jet_bounds
      hK hKU (by norm_num : (0 : ℝ) < 1 / 2)
  let A : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] RoundCylinderCoordinates :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨B, hB, htime⟩ := exists_eventually_terminal_parametrizedJet_time_constant C F p
    P hc hop radius hradius hbound A d Z (a := 1 / 2) (b := 7) (by norm_num) (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro δ s hδ hδone hs hsone G hcomplete Φ hΦ hround
  let Fseq (k : ℕ) := (F k).bufferedExpandingFlow δ
  have hab : (-1 : ℝ) < δ / 2 := by linarith
  have hbδ : δ / 2 ≤ δ := by linarith
  have hsub : ∀ k : ℕ, Ioo (-1) (δ / 2) ⊆ (fun t : ℝ => t - δ) ⁻¹' Iic 0 := by
    intro k t ht
    change t - δ ≤ 0
    linarith [ht.2]
  let W := G.window Fseq hab hbδ 0 hsub
  have hzero : (-1 : ℝ) < 0 ∧ 0 < δ / 2 := ⟨by norm_num, by linarith⟩
  have hcompact : IsCompact (Φ '' (univ ×ˢ J)) :=
    (isCompact_univ.prod hJ).image hΦ.contMDiff.continuous
  obtain ⟨R, hR, hdist⟩ := W.exists_pos_eventually_image_subset_ballAt
    hzero hzero hcomplete hcompact
  have hterminaldist : ∀ᶠ i in atTop, ∀ x ∈ Φ '' (univ ×ˢ J),
      ((F (G.subsequence i)).metric 0).edist (p (G.subsequence i))
        (G.embedding i x) ≤ ENNReal.ofReal R := by
    filter_upwards [hdist] with i hi x hx
    have h := hi (mem_image_of_mem (fun y => ((W.embedding i).toFun (0, y)).2) hx)
    change G.embedding i x ∈ ((F (G.subsequence i)).metric (0 + -δ)).ball
      (p (G.subsequence i)) R at h
    rw [zero_add] at h
    exact (ball_subset_terminal C F P hop (G.subsequence i) (-δ) (by linarith)
      (p (G.subsequence i)) R h).le
  have hinitial := hinit W hzero hΦ.contMDiff hzero hs hround d
  have helliptic := W.eventually_cylinder_parametrized_center_ellipticity
    hzero hΦ.contMDiff hzero (rmin := 1 / 2) (rmax := 1)
    (by norm_num) hs hsone hround hJ
  filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually (htime R hR.le),
    hinitial, helliptic, W.eventually_cylinderCover_parametrizations_regular hzero Φ hΦ hK,
    hterminaldist] with i ht hi hell hreg hd q r hr j hj
  obtain ⟨U, hU, hKU', hmap, hinvert⟩ := hreg q
  let e : RoundCylinderCoordinates → (C (G.subsequence i)).carrier :=
    fun y => G.embedding i (Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2))
  have hx : (0, r) ∈ U := hKU' ⟨rfl, hr⟩
  have hd' : ((F (G.subsequence i)).metric 0).edist (p (G.subsequence i)) (e (0, r)) ≤
      ENNReal.ofReal R := by
    simpa only [e, Poincare.Geometry.Riemannian.SpaceForm.sphere_chart_symm_zero] using
      hd (Φ (q, r)) (mem_image_of_mem Φ ⟨mem_univ _, hr⟩)
  apply ht hU hmap hinvert hδ hδone hx hd' ?_ ?_ j hj
  · intro v
    have h := hell q r hr v
    change (1 : ℝ)⁻¹ / 2 * ‖v‖ ^ 2 ≤
        ((F (G.subsequence i)).metric (0 + -δ)).parametrizedCoefficients e (0, r) v v ∧
      ((F (G.subsequence i)).metric (0 + -δ)).parametrizedCoefficients e (0, r) v v ≤
        (3 * (1 / 2 : ℝ)⁻¹ + 1) * ‖v‖ ^ 2 at h
    norm_num at h
    exact h
  · intro l hl
    have h := hi l hl q (0, r) ⟨rfl, hr⟩
    change ‖iteratedFDeriv ℝ l
      (((F (G.subsequence i)).metric (0 + -δ)).parametrizedCoefficients e) (0, r)‖ ≤ Z l at h
    rwa [zero_add] at h

end PoincareConjecture.RawAncientSequence
