import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallBackwardLimit
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.CoordinateCurvature










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter PoincareConjecture.ChartDistance PoincareConjecture.SpacetimeBounds
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  {H : CounterexampleNeckFamily E} {T : ∀ k, SourceTubeData (H.segment k)}
  {A1 : ℝ} {hA1 : 0 < A1} {phi : ℕ → ℕ}
  {G : RegularPointedMetricConvergence
    (fun k => H.tubeCriticalMetric T A1 (phi k))
    (fun k => H.tubeCriticalBase T A1 hA1 (phi k))}
  {q : G.limitCarrier.carrier} {a : ℝ}
  (D : CriticalBallBackwardChartData H T A1 hA1 phi G q a)



theorem limitParametrization_smooth (k : ℕ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (D.limitParametrization k) D.limitDomain := by
  let := D.limitDomain_open.isOpenEmbedding_subtypeVal.singletonChartedSpace
  exact contMDiffOn_chartParametrization (fun _ : Unit => D.limitDomain)
    (fun _ => D.limitDomain_open) (D.limitNeckMap_localDiffeomorph k).contMDiff

set_option maxHeartbeats 1000000 in



theorem limitParametrization_invertible (k : ℕ) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ D.limitDomain) :
    (mfderiv (𝓡 3) (𝓡 3) (D.limitParametrization k) x).IsInvertible := by
  have heq : D.limitParametrization k =ᶠ[𝓝 x] D.parametrization k :=
    Filter.mem_of_superset (D.limitDomain_open.mem_nhds hx) (D.limitParametrization_eq k)
  rw [heq.mfderiv_eq]
  exact D.parametrization_invertible k (D.limitDomain_subset_domain hx)

variable {D}

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 1800000 in



theorem BackwardChartLimit.spatial_twoJets (L : BackwardChartLimit D)
    (t : ℝ) (ht : t ∈ Icc (-(a / 8)) 0) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ D.limitDomain) :
    Tendsto (fun k => metricTwoJet
      (((D.sourceFlow (L.subsequence k)).metric t).pullbackCoefficients
        (D.limitParametrization (L.subsequence k))) x) atTop
      (𝓝 (metricTwoJet (fun y => L.coefficients (t, y)) x)) := by
  have hJ : UniqueDiffOn ℝ (Icc (-(a / 8)) 0) :=
    uniqueDiffOn_Icc (by linarith [D.scale_pos])
  have hs (k : ℕ) : ContDiffOn ℝ ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
        ((D.sourceFlow k).metric z.1).pullbackCoefficients (D.limitParametrization k) z.2)
      (Icc (-(a / 8)) 0 ×ˢ D.limitDomain) :=
    (D.sourceFlow k).smooth.contDiffOn_spacetime_pullbackCoefficients_within
      D.limitDomain_open (D.limitParametrization_smooth k)
  apply tendsto_metricTwoJet_of_uniform_bilinear_jets (K := {x}) _ (mem_singleton x)
  intro m _
  have hsub : {(t, x)} ⊆ Icc (-(a / 8)) 0 ×ˢ D.limitDomain :=
    singleton_subset_iff.mpr ⟨ht, hx⟩
  have h := (L.jets m {(t, x)} isCompact_singleton hsub).iteratedFDeriv_spatial_slice
    hJ D.limitDomain_open hsub (Eventually.of_forall fun k => hs (L.subsequence k))
    L.coefficients_smooth (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top))
  apply (h.comp (fun y => (t, y))).mono
  intro y hy
  rcases mem_singleton_iff.mp hy with rfl
  exact mem_singleton (t, y)

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 2400000 in



theorem BackwardChartLimit.curvatureTensor_tendsto (L : BackwardChartLimit D) :
    letI := D.limitDomain_open.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := D.limitDomain_open.isOpenEmbedding_subtypeVal.isManifold_singleton
      (I := 𝓡 3) (n := ∞)
    ∀ t ∈ Icc (-(a / 8)) 0, ∀ (x : D.limitDomain) (v w y z : EuclideanSpace ℝ (Fin 3)),
      Tendsto (fun k => ((D.sourceFlow (L.subsequence k)).connection t).curvatureTensor
        (D.limitParametrization (L.subsequence k) x)
        (mfderiv (𝓡 3) (𝓡 3) (D.limitParametrization (L.subsequence k)) x v)
        (mfderiv (𝓡 3) (𝓡 3) (D.limitParametrization (L.subsequence k)) x w)
        (mfderiv (𝓡 3) (𝓡 3) (D.limitParametrization (L.subsequence k)) x y)
        (mfderiv (𝓡 3) (𝓡 3) (D.limitParametrization (L.subsequence k)) x z)) atTop
        (𝓝 ((L.flow.connection t).curvatureTensor x v w y z)) := by
  let := D.limitDomain_open.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := D.limitDomain_open.isOpenEmbedding_subtypeVal.isManifold_singleton
    (I := 𝓡 3) (n := ∞)
  intro t ht x v w y z
  let c := extChartAt (𝓡 3) x
  have hc : c.target = D.limitDomain :=
    canonical_extChartAt_target (fun _ : Unit => D.limitDomain)
      (fun _ => D.limitDomain_open) () x
  have hs : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm D.limitDomain := by
    exact (contMDiffOn_extChartAt_symm x).mono (fun _ hp => hc.symm ▸ hp)
  have hi (p) (hp : p ∈ D.limitDomain) :
      (mfderiv (𝓡 3) (𝓡 3) c.symm p).IsInvertible := by
    have hp' : p ∈ c.target := hc.symm ▸ hp
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hp'
  have hnear : (L.flow.metric t).pullbackCoefficients c.symm =ᶠ[𝓝 (x.val)]
      (fun p => L.coefficients (t, p)) := by
    filter_upwards [D.limitDomain_open.mem_nhds x.property] with p hp
    rw [RiemannianMetric.pullbackCoefficients_canonicalChart D.limitDomain
      D.limitDomain_open (L.flow.metric t) x ⟨p, hp⟩]
    ext u v
    exact L.metric_coefficients t ht ⟨p, hp⟩ u v
  have hj := L.spatial_twoJets t ht x.property
  have hconv := tendsto_curvatureTensor_of_pullback_jets
    (fun k => (D.sourceFlow (L.subsequence k)).connection t) (L.flow.connection t)
    D.limitDomain_open x.property
    (fun k => D.limitParametrization_smooth (L.subsequence k))
    (fun k _ hp => D.limitParametrization_invertible (L.subsequence k) hp) hs hi
    (by simpa only [metricTwoJet, hnear.self_of_nhds] using hj.fst_nhds)
    (by simpa only [metricTwoJet, hnear.fderiv_eq] using hj.snd_nhds.fst_nhds)
    (by simpa only [metricTwoJet, hnear.fderiv.fderiv_eq]
      using hj.snd_nhds.snd_nhds) v w y z
  have hd := mfderivWithin_range_extChartAt_symm (I := 𝓡 3) (x := x)
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hd
  change mfderiv (𝓡 3) (𝓡 3) c.symm (x.val) = ContinuousLinearMap.id ℝ _ at hd
  have hx : c.symm x.val = x := (extChartAt (𝓡 3) x).left_inv (mem_extChartAt_source x)
  have hvalue : (L.flow.connection t).curvatureTensor (c.symm x.val)
      (mfderiv (𝓡 3) (𝓡 3) c.symm x.val v) (mfderiv (𝓡 3) (𝓡 3) c.symm x.val w)
      (mfderiv (𝓡 3) (𝓡 3) c.symm x.val y) (mfderiv (𝓡 3) (𝓡 3) c.symm x.val z) =
      (L.flow.connection t).curvatureTensor x v w y z := by
    rw [hd]
    change (L.flow.connection t).curvatureTensor (c.symm x.val) v w y z = _
    exact congrArg (fun p : D.limitDomain => (L.flow.connection t).curvatureTensor p
      (show EuclideanSpace ℝ (Fin 3) from v) w y z) hx
  simpa only [hvalue] using hconv

end PoincareConjecture.M28.CounterexampleNeckFamily.CriticalBallBackwardChartData
