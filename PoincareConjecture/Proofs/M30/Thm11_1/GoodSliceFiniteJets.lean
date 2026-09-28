import PoincareConjecture.Definitions.M28BoundedDistance
import PoincareConjecture.Proofs.M04.ScalarEvolution
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinMetricCoefficients
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.Parabolic.SpatialContinuity
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.UniformSpace.HeineCantor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v w

namespace PoincareConjecture.M30

set_option maxHeartbeats 800000 in

theorem exists_good_slice_with_finite_metric_jets
    (F : GeneralizedRicciFlowData.{u}) {epsilon C t : ℝ}
    (htF : t ∈ F.interval) (xbase : (F.slice t).carrier)
    (hdense : generalizedEarlierDenseStrongCanonicalNeighborhoods F epsilon C t xbase)
    {Q T : ℝ} (hQ : 0 < Q) (hT : 0 < T)
    {Y : Type v} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y] [IsManifold (𝓡 3) ∞ Y]
    (P : RicciFlow 3 Y (Icc (-T) 0))
    {ι : Type w} [Finite ι]
    (U Kchart : ι → Set (EuclideanSpace ℝ (Fin 3)))
    (hU : ∀ i, IsOpen (U i)) (hKchart : ∀ i, IsCompact (Kchart i))
    (hKU : ∀ i, Kchart i ⊆ U i)
    (ψ : ι → EuclideanSpace ℝ (Fin 3) → Y)
    (hψ : ∀ i, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (ψ i) (U i))
    (K : Set Y) (hK : IsCompact K) (d : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    ∃ s : ℝ, s ∈ Icc (-T) 0 ∧ -delta < s ∧ t + s / Q ∈ F.interval ∧
      generalizedSliceStrongCanonicalNeighborhoods F epsilon C
        (4 * F.scalar ⟨t, xbase⟩) (t + s / Q) ∧
      (∀ i m, m ≤ d → ∀ z ∈ Kchart i,
        ‖iteratedFDeriv ℝ m ((P.metric s).pullbackCoefficients (ψ i)) z -
          iteratedFDeriv ℝ m ((P.metric 0).pullbackCoefficients (ψ i)) z‖ < delta) ∧
      ∀ y ∈ K, |(P.connection s).scalarCurvature y -
        (P.connection 0).scalarCurvature y| < delta := by
  let J : Set ℝ := Icc (-T) 0
  have hzero : (0 : ℝ) ∈ J := ⟨by linarith, le_rfl⟩
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_Icc (by linarith)
  have hjet (i : ι) (m : ℕ) : ∀ᶠ s in 𝓝[J] (0 : ℝ), ∀ z ∈ Kchart i,
      ‖iteratedFDeriv ℝ m ((P.metric s).pullbackCoefficients (ψ i)) z -
        iteratedFDeriv ℝ m ((P.metric 0).pullbackCoefficients (ψ i)) z‖ < delta := by
    have hcoeff := P.smooth.contDiffOn_spacetime_pullbackCoefficients_within
      (hU i) (hψ i)
    have hcontinuous := M28.continuousOn_spatialJet_of_within hJ (hU i) hcoeff m
    obtain ⟨V, hV, hclose⟩ := (hKchart i).mem_uniformity_of_prod
      (f := fun s z => iteratedFDeriv ℝ m
        ((P.metric s).pullbackCoefficients (ψ i)) z)
      (s := J) (hcontinuous.mono (Set.prod_mono_right (hKU i))) hzero
      (Metric.dist_mem_uniformity hdelta)
    filter_upwards [hV] with s hs
    intro z hz
    simpa only [Set.mem_ofPred_eq, dist_eq_norm] using! hclose s hs z hz
  have hscalar : ∀ᶠ s in 𝓝[J] (0 : ℝ), ∀ y ∈ K,
      |(P.connection s).scalarCurvature y -
        (P.connection 0).scalarCurvature y| < delta := by
    have hcontinuous := P.contMDiffOn_scalarCurvature.continuousOn
    obtain ⟨V, hV, hclose⟩ := hK.mem_uniformity_of_prod
      (f := fun s y => (P.connection s).scalarCurvature y)
      (s := J) (hcontinuous.mono (Set.prod_mono_right (subset_univ K))) hzero
      (Metric.dist_mem_uniformity hdelta)
    filter_upwards [hV] with s hs
    intro y hy
    simpa only [Set.mem_ofPred_eq, Real.dist_eq] using! hclose s hs y hy
  have hfinite : ∀ᶠ s in 𝓝[J] (0 : ℝ), ∀ i, ∀ m : Fin (d + 1), ∀ z ∈ Kchart i,
      ‖iteratedFDeriv ℝ (m : ℕ) ((P.metric s).pullbackCoefficients (ψ i)) z -
        iteratedFDeriv ℝ (m : ℕ) ((P.metric 0).pullbackCoefficients (ψ i)) z‖ < delta :=
    Filter.eventually_all.mpr fun i =>
      Filter.eventually_all.mpr fun m : Fin (d + 1) => hjet i m
  obtain ⟨radius, hradius, hnear⟩ :=
    Metric.mem_nhdsWithin_iff.mp (hfinite.and hscalar)
  let b := min T (min delta radius)
  have hb : 0 < b := lt_min hT (lt_min hdelta hradius)
  have hbT : b ≤ T := min_le_left _ _
  have hbdelta : b ≤ delta := (min_le_right _ _).trans (min_le_left _ _)
  have hbradius : b ≤ radius := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨u, huF, hulower, hupper, hgood⟩ :=
    hdense t htF le_rfl (t - b / Q) (sub_lt_self _ (div_pos hb hQ))
  let s := Q * (u - t)
  have hslower : -b < s := by
    have hdiv : -b / Q < u - t := by
      rw [neg_div]
      linarith
    have hmul := (div_lt_iff₀ hQ).mp hdiv
    simpa only [s, mul_comm] using hmul
  have hsupper : s ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hQ.le (sub_nonpos.mpr hupper)
  have hsJ : s ∈ J := ⟨by linarith, hsupper⟩
  have hclock : t + s / Q = u := by
    dsimp only [s]
    field_simp [hQ.ne']
    ring
  have hsball : s ∈ Metric.ball (0 : ℝ) radius := by
    change dist s 0 < radius
    rw [Real.dist_eq, sub_zero, abs_of_nonpos hsupper]
    linarith
  obtain ⟨hjets, hscalars⟩ := hnear ⟨hsball, hsJ⟩
  refine ⟨s, hsJ, by linarith, ?_, ?_, ?_, hscalars⟩
  · rwa [hclock]
  · rwa [hclock]
  · intro i m hm z hz
    exact hjets i ⟨m, by omega⟩ z hz

end PoincareConjecture.M30
