import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.RetainedSpatialBounds
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.WithinJetBoundsService













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space
  FlowCarrier.secondCountable

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 800000 in




theorem exists_retained_local_coefficient_bounds
    (hMixed : WithinFlowJetBoundsService.{0, 0})
    {T τ : ℝ} (hτ : 0 < τ) (hτT : τ < T) (hT1 : T ≤ 1)
    {S : PointedFlowSequence 3 (-T / 2) (T / 2)}
    (G : PointedGeometricConvergence S)
    (Fsrc : ∀ k, RicciFlow 3 (S.carrier k).carrier (Icc (-T) 0))
    (hmetric : ∀ k t, (Fsrc k).metric t =
      (S.flow k).flow.metric (t + T / 2)) :
    let e := fun (q : G.limitCarrier.carrier) (k : ℕ) =>
      (fun y => ((G.embedding k).toFun (0, y)).2) ∘
        (extChartAt (𝓡 3) q).symm
    let f := fun (q : G.limitCarrier.carrier) (k : ℕ)
        (z : ℝ × EuclideanSpace ℝ (Fin 3)) =>
      ((Fsrc (G.subsequence k)).metric z.1).pullbackCoefficients (e q k) z.2
    (∀ (q : G.limitCarrier.carrier)
      (K : Set (EuclideanSpace ℝ (Fin 3))),
      IsCompact K → K ⊆ (extChartAt (𝓡 3) q).target →
      ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop,
        ∀ t ∈ Icc (-T) 0, ∀ x ∈ K,
          ((Fsrc (G.subsequence k)).connection t).curvatureDerivativeNorm j
            (e q k x) ≤ C) →
    ∀ (q : G.limitCarrier.carrier) (x₀ : EuclideanSpace ℝ (Fin 3)),
      x₀ ∈ (extChartAt (𝓡 3) q).target →
      ∃ r : ℝ, 0 < r ∧
        Metric.closedBall x₀ r ⊆ (extChartAt (𝓡 3) q).target ∧
        ∃ α : ℝ, 0 < α ∧
          (∀ᶠ k : ℕ in atTop,
            ∀ z ∈ Icc (-τ) 0 ×ˢ Metric.closedBall x₀ r,
            ∀ v : EuclideanSpace ℝ (Fin 3),
              α * ‖v‖ ^ 2 ≤ f q k z v v) ∧
          (∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop,
            ∀ z ∈ Icc (-τ) 0 ×ˢ Metric.closedBall x₀ r,
              ‖iteratedFDerivWithin ℝ m (f q k)
                (Icc (-τ) 0 ×ˢ Metric.closedBall x₀ r) z‖ ≤ C) := by
  classical
  intro e f hcurv q x₀ hx₀
  have hT : 0 < T := hτ.trans hτT
  have hzero : -T / 2 < 0 ∧ 0 < T / 2 := ⟨by linarith, by linarith⟩
  let c := extChartAt (𝓡 3) q
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_extChartAt_target (I := 𝓡 3) q) x₀ hx₀
  let r : ℝ := ε / 2
  have hr : 0 < r := half_pos hε
  let K := Metric.closedBall x₀ r
  have hK : IsCompact K := isCompact_closedBall x₀ r
  have hKc : K ⊆ c.target :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  obtain ⟨α, β, hα, _hβ, hell, hspatial⟩ :=
    exists_eventually_retained_closed_spatial_bounds hT hT1 G Fsrc hmetric
      q hK hKc (hcurv q K hK hKc)
  have hsmall : Icc (-τ) (0 : ℝ) ⊆ Icc (-T) 0 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  let ψ (k : ℕ) : G.limitCarrier.carrier → (S.carrier (G.subsequence k)).carrier :=
    fun y => ((G.embedding k).toFun (0, y)).2
  let U (k : ℕ) : Set (EuclideanSpace ℝ (Fin 3)) :=
    c.target ∩ c.symm ⁻¹' G.exhaustion k
  have hU (k : ℕ) : IsOpen (U k) :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target (I := 𝓡 3) q) (G.exhaustion_open k)
  have hchart {y : EuclideanSpace ℝ (Fin 3)} (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hmap (k : ℕ) {y : EuclideanSpace ℝ (Fin 3)}
      (hy : c.symm y ∈ G.exhaustion k) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ (ψ k) (c.symm y) :=
    (G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hzero hy
  have he (k : ℕ) : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e q k) (U k) := by
    intro y hy
    exact ((hmap k hy.2).comp y (hchart hy.1)).contMDiffWithinAt
  have hi (k : ℕ) (y : EuclideanSpace ℝ (Fin 3)) (hy : y ∈ U k) :
      (mfderiv (𝓡 3) (𝓡 3) (e q k) y).IsInvertible := by
    have hbij := (G.embedding k).spatialMap_mfderiv_bijective
      (G.exhaustion_open k) hzero hy.2
    let D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      mfderiv (𝓡 3) (𝓡 3) (ψ k) (c.symm y)
    have hD : D.IsInvertible :=
      ⟨ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hbij.1)
        (LinearMap.range_eq_top.mpr hbij.2), rfl⟩
    have hc : (mfderiv (𝓡 3) (𝓡 3) c.symm y).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm hy.1
    change (mfderiv (𝓡 3) (𝓡 3) (ψ k ∘ c.symm) y).IsInvertible
    rw [mfderiv_comp y ((hmap k hy.2).mdifferentiableAt (by simp))
      ((hchart hy.1).mdifferentiableAt (by simp))]
    exact hD.comp hc
  let V (k : ℕ) := K ∩ U k
  let Ti (k : ℕ) := Ioo (-T) (0 : ℝ) ×ˢ V k
  let Sc (k : ℕ) := Icc (-T) (0 : ℝ) ×ˢ V k
  have hJ : UniqueDiffOn ℝ (Icc (-T) (0 : ℝ)) :=
    uniqueDiffOn_Icc (by linarith)
  have hTi (k : ℕ) : Ti k ⊆ interior (Icc (-T) (0 : ℝ)) ×ˢ U k := by
    intro z hz
    rw [interior_Icc]
    exact ⟨hz.1, hz.2.2⟩
  have hSc (k : ℕ) : Sc k ⊆
      (Icc (-T) (0 : ℝ) ×ˢ U k) ∩ closure (Ti k) := by
    intro z hz
    refine ⟨⟨hz.1, hz.2.2⟩, ?_⟩
    change z ∈ closure (Ioo (-T) (0 : ℝ) ×ˢ V k)
    rw [closure_prod_eq, closure_Ioo (show -T ≠ (0 : ℝ) by linarith)]
    exact ⟨hz.1, subset_closure hz.2⟩
  have hsp : ∀ d : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop,
      ∀ z ∈ Ti k, ∀ j ≤ d,
        ‖iteratedFDeriv ℝ j
          (((Fsrc (G.subsequence k)).metric z.1).pullbackCoefficients (e q k))
          z.2‖ ≤ B := by
    intro d
    obtain ⟨B, hB, hb⟩ := hspatial d
    refine ⟨B, hB, ?_⟩
    filter_upwards [hb] with k hk z hz j hj
    exact (hk z.2 hz.2.1 j hj).1 z.1 (Ioo_subset_Icc_self hz.1)
  have hellTi : ∀ᶠ k : ℕ in atTop, ∀ z ∈ Ti k, ∀ v,
      α * ‖v‖ ^ 2 ≤
        ((Fsrc (G.subsequence k)).metric z.1).pullbackCoefficients (e q k) z.2 v v := by
    filter_upwards [hell] with k hk z hz v
    exact (hk z.1 (Ioo_subset_Icc_self hz.1) z.2 hz.2.1 v).1
  have hmixed := hMixed atTop (fun _ : ℕ => Icc (-T) 0)
    (fun k => Fsrc (G.subsequence k)) U (e q) Ti Sc
    (fun _ => hJ) hU he hi hTi hSc hsp hα hellTi
  have hcK : ContinuousOn c.symm K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  obtain ⟨N, hN⟩ := G.exists_exhaustion_superset (hK.image_of_continuousOn hcK)
  have hKU (k : ℕ) (hk : N ≤ k) : K ⊆ U k := by
    intro x hx
    exact ⟨hKc hx, G.exhaustion_monotone hk (hN (mem_image_of_mem _ hx))⟩
  let Ω := Icc (-τ) (0 : ℝ) ×ˢ K
  have hKunique : UniqueDiffOn ℝ K := uniqueDiffOn_convex (convex_closedBall x₀ r)
    ⟨x₀, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self hr)⟩
  have hΩunique : UniqueDiffOn ℝ Ω :=
    (uniqueDiffOn_Icc (show -τ < (0 : ℝ) by linarith)).prod hKunique
  refine ⟨r, hr, hKc, α, hα, ?_, ?_⟩
  · filter_upwards [hell] with k hk z hz v
    exact (hk z.1 (hsmall hz.1) z.2 hz.2 v).1
  · intro m
    obtain ⟨C, hC, hbound⟩ := hmixed m
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound, eventually_ge_atTop N] with k hk hkN z hz
    have hΩD : Ω ⊆ Icc (-T) (0 : ℝ) ×ˢ U k :=
      prod_mono hsmall (hKU k hkN)
    have hDunique := hJ.prod (hU k).uniqueDiffOn
    have hsmooth : ContDiffOn ℝ m (f q k) (Icc (-T) 0 ×ˢ U k) :=
      ((Fsrc (G.subsequence k)).contDiffOn_pullbackCoefficients_within
        (hU k) (he k)).of_le (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)
    rw [iteratedFDerivWithin_subset hΩD hΩunique hDunique hsmooth hz]
    exact hk z ⟨hsmall hz.1, hz.2, hKU k hkN hz.2⟩

end PoincareConjecture.M30
