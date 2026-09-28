import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Coordinates.EmbeddingBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Jets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.MetricComparison
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Embedding.SpatialRegularity















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M30

open NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {a b : ℝ} {S : PointedFlowSequence 3 a b}

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 1000000 in



theorem exists_eventually_reference_spatial_jet_bound
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    (q : G.limitCarrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m
        (((S.flow (G.subsequence k)).flow.metric 0).pullbackCoefficients
          ((fun y => ((G.embedding k).toFun (0, y)).2) ∘
            (extChartAt (𝓡 3) q).symm)) x‖ ≤ B := by
  classical
  let c := extChartAt (𝓡 3) q
  let ψ (k : ℕ) : G.limitCarrier.carrier → (S.carrier (G.subsequence k)).carrier :=
    fun y => ((G.embedding k).toFun (0, y)).2
  let f (k : ℕ) (i j : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :=
    G.limitCarrier.coordinateCoefficient q
      (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)) i j (0, x)
  let g (i j : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :=
    G.limitCarrier.coordinateCoefficient q
      (fun t y v w => G.limitCarrier.metricInner (G.limitFlow.metricAt t) y v w) i j (0, x)
  have hconv (i j : Fin 3) : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (f k i j)) (iteratedFDeriv ℝ m (g i j)) atTop K :=
    G.tendstoUniformlyOn_coordinate_spatial_metricJet q m i j 0 hzero K hK hKc
  have hdiff (i j : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ K) :
      ContDiffAt ℝ ∞ (g i j) x :=
    (G.limitFlow.contDiffAt_coordinateCoefficient_metric q i j (0, x) hzero (hKc hx)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  have hcomponent (i j : Fin 3) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop,
      ∀ x ∈ K, ‖iteratedFDeriv ℝ m (f k i j) x‖ ≤ B := by
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
      (fun x hx => ((hdiff i j x hx).continuousAt_iteratedFDeriv
        (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)).continuousWithinAt)
    refine ⟨max (B + 1) 0, le_max_right _ _, ?_⟩
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hconv i j) 1 zero_lt_one]
      with k hk x hx
    apply le_trans _ (le_max_left (B + 1) 0)
    exact (norm_le_norm_add_norm_sub (iteratedFDeriv ℝ m (g i j) x)
      (iteratedFDeriv ℝ m (f k i j) x)).trans
        (add_le_add (hB x hx) (by simpa only [dist_eq_norm] using (hk x hx).le))
  choose B hB hbound using hcomponent
  let C := ∑ i : Fin 3, ∑ j : Fin 3, B i j
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hB i j
  have hBC (i j : Fin 3) : B i j ≤ C := by
    apply (Finset.single_le_sum (fun j _ => hB i j) (Finset.mem_univ j)).trans
    exact Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => hB i j)
      (Finset.mem_univ i)
  obtain ⟨D, hD, hnorm⟩ := exists_bilinear_jet_norm_le_components
    (EuclideanSpace ℝ (Fin 3)) m
  have hc : ContinuousOn c.symm K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (hK.image_of_continuousOn hc)
  refine ⟨D * C, mul_nonneg hD.le hC, ?_⟩
  filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hbound i)),
    eventually_ge_atTop j] with k hk hjk x hx
  let gk := (S.flow (G.subsequence k)).flow.metric 0
  let A := gk.pullbackCoefficients (ψ k ∘ c.symm)
  have hxstage := G.exhaustion_monotone hjk (hj (mem_image_of_mem _ hx))
  have hcx := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q (hKc hx)).contMDiffAt
    (extChartAt_target_mem_nhds' (hKc hx))
  have hψ := (G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hzero hxstage
  have hA : ContDiffAt ℝ ∞ A x := gk.contDiffAt_pullbackCoefficients (hψ.comp x hcx)
  apply hnorm _ C hC
  intro i l
  have heq : f k i l =ᶠ[𝓝 x] coefficientEval i l ∘ A := by
    filter_upwards [extChartAt_target_mem_nhds' (hKc hx),
      hcx.continuousAt.preimage_mem_nhds ((G.exhaustion_open k).mem_nhds hxstage)]
      with y hy hye
    have hcy := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
    have hψy := (G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hzero hye
    have hd : mfderiv (𝓡 3) (𝓡 3) (ψ k ∘ c.symm) y =
        (mfderiv (𝓡 3) (𝓡 3) (ψ k) (c.symm y)).comp
          (mfderiv (𝓡 3) (𝓡 3) c.symm y) :=
      mfderiv_comp y (hψy.mdifferentiableAt (by simp)) (hcy.mdifferentiableAt (by simp))
    change gk.inner (ψ k (c.symm y))
        (mfderiv (𝓡 3) (𝓡 3) (ψ k) (c.symm y)
          (mfderiv (𝓡 3) (𝓡 3) c.symm y (EuclideanSpace.basisFun (Fin 3) ℝ i)))
        (mfderiv (𝓡 3) (𝓡 3) (ψ k) (c.symm y)
          (mfderiv (𝓡 3) (𝓡 3) c.symm y (EuclideanSpace.basisFun (Fin 3) ℝ l))) =
      gk.inner (ψ k (c.symm y))
        (mfderiv (𝓡 3) (𝓡 3) (ψ k ∘ c.symm) y (EuclideanSpace.basisFun (Fin 3) ℝ i))
        (mfderiv (𝓡 3) (𝓡 3) (ψ k ∘ c.symm) y (EuclideanSpace.basisFun (Fin 3) ℝ l))
    rw [hd]
    rfl
  have hderiv := (heq.iteratedFDeriv ℝ m).self_of_nhds
  rw [(coefficientEval i l).iteratedFDeriv_comp_left hA
    (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)] at hderiv
  exact (hderiv ▸ hk i l x hx).trans (hBC i l)

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 800000 in



theorem exists_eventually_reference_ellipticity
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    (q : G.limitCarrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 3) q).target) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ ∀ᶠ k : ℕ in atTop, ∀ x ∈ K, ∀ v,
      α * ‖v‖ ^ 2 ≤ ((S.flow (G.subsequence k)).flow.metric 0).pullbackCoefficients
        ((fun y => ((G.embedding k).toFun (0, y)).2) ∘ (extChartAt (𝓡 3) q).symm) x v v ∧
      ((S.flow (G.subsequence k)).flow.metric 0).pullbackCoefficients
        ((fun y => ((G.embedding k).toFun (0, y)).2) ∘ (extChartAt (𝓡 3) q).symm) x v v ≤
          β * ‖v‖ ^ 2 := by
  let c := extChartAt (𝓡 3) q
  let B := (G.limitFlow.flow.metric 0).pullbackCoefficients c.symm
  have hchart {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ K) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm x :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q (hKc hx)).contMDiffAt
      (extChartAt_target_mem_nhds' (hKc hx))
  have hB : ContinuousOn B K := fun x hx =>
    ((G.limitFlow.flow.metric 0).contDiffAt_pullbackCoefficients
      (hchart hx)).continuousAt.continuousWithinAt
  have hpos : ∀ x ∈ K, ∀ v : EuclideanSpace ℝ (Fin 3), v ≠ 0 → 0 < B x v v := by
    intro x hx v hv
    apply (G.limitFlow.flow.metric 0).pos
    have hi : (mfderiv (𝓡 3) (𝓡 3) c.symm x).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm (hKc hx)
    intro hz
    apply hv
    apply hi.injective
    rw [map_zero]
    convert! hz using 1
  obtain ⟨α, hα, hlower⟩ := exists_uniform_bilinear_family_lower_bound hK hB hpos
  obtain ⟨β, hβ⟩ := hK.exists_bound_of_continuousOn (f := B) hB
  have hc : ContinuousOn c.symm K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  have himage := hK.image_of_continuousOn hc
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset himage
  refine ⟨α / 2, 2 * max β 1, by positivity, by positivity, ?_⟩
  filter_upwards [G.eventually_pullback_inner_bounds himage hzero
    (by norm_num : (0 : ℝ) < 1 / 2), eventually_ge_atTop j] with k hk hjk x hx v
  let ψ : G.limitCarrier.carrier → (S.carrier (G.subsequence k)).carrier :=
    fun y => ((G.embedding k).toFun (0, y)).2
  let w := mfderiv (𝓡 3) (𝓡 3) c.symm x v
  have hcomparison := hk (c.symm x) (mem_image_of_mem _ hx) w
  have he := (G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k) hzero
    (G.exhaustion_monotone hjk (hj (mem_image_of_mem _ hx)))
  have hd : mfderiv (𝓡 3) (𝓡 3) (ψ ∘ c.symm) x =
      (mfderiv (𝓡 3) (𝓡 3) ψ (c.symm x)).comp (mfderiv (𝓡 3) (𝓡 3) c.symm x) :=
    mfderiv_comp x (he.mdifferentiableAt (by simp)) ((hchart hx).mdifferentiableAt (by simp))
  have heq : pullbackInnerValue G.limitFlow (S.flow (G.subsequence k))
      (G.embedding k) 0 (c.symm x) w w =
      ((S.flow (G.subsequence k)).flow.metric 0).pullbackCoefficients (ψ ∘ c.symm) x v v := by
    unfold RiemannianMetric.pullbackCoefficients
    rw [hd]
    rfl
  have href : G.limitCarrier.metricInner (G.limitFlow.metricAt 0) (c.symm x) w w =
      B x v v := rfl
  rw [heq, href] at hcomparison
  have hupper : B x v v ≤ max β 1 * ‖v‖ ^ 2 := by
    apply (le_abs_self _).trans
    calc
      |B x v v| ≤ ‖B x‖ * (‖v‖ * ‖v‖) := by
        simpa only [Real.norm_eq_abs, mul_assoc] using (B x).le_opNorm₂ v v
      _ ≤ max β 1 * ‖v‖ ^ 2 := by
        simpa only [pow_two] using
          mul_le_mul_of_nonneg_right ((hβ x hx).trans (le_max_left β 1))
            (mul_nonneg (norm_nonneg v) (norm_nonneg v))
  have hnonneg : 0 ≤ B x v v := le_trans (by positivity) (hlower x hx v)
  constructor
  · nlinarith [hlower x hx v, hcomparison.1]
  · nlinarith [hcomparison.2]

end PoincareConjecture.M30
