import PoincareConjecture.Proofs.M14.Sec6_7_InitialJacobianCoordinates
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeCover











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x y : G.Point} {p : M14BackwardPath G T 0 τ x y}

private theorem metric_pair_heq {q r : G.Point} (h : q = r)
    {v w : G.Horizontal q} {v' w' : G.Horizontal r}
    (hv : HEq v v') (hw : HEq w w') :
    G.spacetime.horizontalMetric.inner q v w =
      G.spacetime.horizontalMetric.inner r v' w' := by
  cases h
  cases hv
  cases hw
  rfl




theorem tendsto_initialJacobi_scaled_pair
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p)
    (Q₁ Q₂ : M14JacobiFieldData G R.curve (M14SqrtParameterInterval 0 τ))
    (hz₁ : Q₁.field 0 = 0) (hz₂ : Q₂.field 0 = 0) :
    Tendsto (fun s : ℝ => (s⁻¹) ^ 2 * G.spacetime.horizontalMetric.inner (R.curve s)
        (Q₁.field s) (Q₂.field s)) (𝓝[>] (0 : ℝ))
      (𝓝 (G.spacetime.horizontalMetric.inner (R.curve 0)
        (M14JacobiFirstDerivative Q₁ 0) (M14JacobiFirstDerivative Q₂ 0))) := by
  have hS : 0 < Real.sqrt τ := Real.sqrt_pos.mpr p.tau_lt
  have hC : M14SqrtParameterInterval 0 τ = Icc 0 (Real.sqrt τ) := by
    simp only [M14SqrtParameterInterval, Real.sqrt_zero]
  have h0C : (0 : ℝ) ∈ M14SqrtParameterInterval 0 τ := by
    rw [hC]
    exact ⟨le_rfl, hS.le⟩
  obtain ⟨b, N, β, hN, h0N, hβ, hrec, hclock⟩ :=
    exists_squareRoot_gauge_neighborhood R h0C
  obtain ⟨l, d, hl, hld, hdS, hl0, h0d, hsubN, _⟩ :=
    M08.exists_enlarged_closed_interval hS le_rfl le_rfl hS.le hN
      (by simpa only [Icc_self, singleton_subset_iff] using h0N)
  have hlzero : l = 0 := le_antisymm hl0 hl
  subst l
  have hsub : Icc 0 d ⊆ M14SqrtParameterInterval 0 τ := by
    rw [hC]
    exact Icc_subset_Icc le_rfl hdS
  have hsub' : Icc 0 d ⊆ M14SqrtParameterInterval 0 τ ∩ N :=
    fun _ hr => ⟨hsub hr, hsubN hr⟩
  have hβ' := hβ.mono hsub'
  have hrec' := fun r hr => hrec r (hsub' hr)
  have hclock' := fun r hr => hclock r (hsub' hr)
  have hR := R.smooth.mono R.interval_subset
  obtain ⟨f, hf, hfQ⟩ := exists_smooth_horizontalGauge_coordinates b hβ' hrec' Q₁.field
    ((pullbackExtension_field_contMDiffOn Q₁.extension hR).mono hsub)
  obtain ⟨g, hg, hgQ⟩ := exists_smooth_horizontalGauge_coordinates b hβ' hrec' Q₂.field
    ((pullbackExtension_field_contMDiffOn Q₂.extension hR).mono hsub)
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  obtain ⟨F⟩ := ordinaryGaugeWitness_nonempty b hCoordinates
  obtain ⟨v, hv, hflim⟩ := tendsto_initialGauge_scaledField R hCoordinates b F hld hsub
    hβ' hrec' hclock' Q₁ hz₁ f hf hfQ
  obtain ⟨w, hw, hglim⟩ := tendsto_initialGauge_scaledField R hCoordinates b F hld hsub
    hβ' hrec' hclock' Q₂ hz₂ g hg hgQ
  let A := fun r => M08.chartActionMetric F.flow T (β 0).2 (r, (β r).2.val)
  have htime (r : ℝ) (hr : r ∈ Icc 0 d) :
      T - r ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock' r hr]
    exact (β r).1.property
  have hpoint := contDiffOn_id.prodMk (gaugeLift_spatialCurve_contDiffOn b hβ')
  have hmap : MapsTo (fun r => (r, (β r).2.val)) (Icc 0 d)
      (Icc 0 d ×ˢ (extChartAt (𝓡 n) (β 0).2).target) := by
    intro r hr
    refine ⟨hr, ?_⟩
    have hsrc : (β r).2 ∈ (extChartAt (𝓡 n) (β 0).2).source := by
      rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
      exact mem_univ _
    have he : extChartAt (𝓡 n) (β 0).2 (β r).2 = (β r).2.val := by
      rw [extChartAt_coe]
      rfl
    simpa only [he] using (extChartAt (𝓡 n) (β 0).2).map_source hsrc
  have hA : ContDiffOn ℝ ∞ A (Icc 0 d) :=
    (M08.chartActionMetric_closed_contDiffOn F.flow T (β 0).2 htime).comp hpoint hmap
  have h0 : (0 : ℝ) ∈ Icc 0 d := ⟨le_rfl, hld.le⟩
  have hAlim := (hA.continuousOn 0 h0).mono Ioc_subset_Icc_self
  change Tendsto A (𝓝[Ioc 0 d] (0 : ℝ)) (𝓝 (A 0)) at hAlim
  rw [nhdsWithin_Ioc_eq_nhdsGT hld] at hAlim
  have hpair (r : ℝ) (hr : r ∈ Icc 0 d) :
      G.spacetime.horizontalMetric.inner (R.curve r) (Q₁.field r) (Q₂.field r) =
        A r (f r) (g r) :=
    (metric_pair_heq (hrec' r hr).symm (hfQ r hr) (hgQ r hr)).trans
      (gauge_chartActionMetric b F T (β 0).2 (β r).2 r (β r).1
        (hclock' r hr).symm (f r) (g r)).symm
  have hvalue : G.spacetime.horizontalMetric.inner (R.curve 0)
      (M14JacobiFirstDerivative Q₁ 0) (M14JacobiFirstDerivative Q₂ 0) = A 0 v w :=
    (metric_pair_heq (hrec' 0 h0).symm hv hw).trans
      (gauge_chartActionMetric b F T (β 0).2 (β 0).2 0 (β 0).1
        (hclock' 0 h0).symm v w).symm
  have hleft := (isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.tendsto (A 0, v)
  have hright := (isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.tendsto (A 0 v, w)
  have hlim := hright.comp ((hleft.comp (hAlim.prodMk_nhds hflim)).prodMk_nhds hglim)
  rw [← hvalue] at hlim
  apply hlim.congr'
  filter_upwards [Ioc_mem_nhdsGT hld] with r hr
  rw [hpair r (Ioc_subset_Icc_self hr)]
  change A r (r⁻¹ • f r) (r⁻¹ • g r) = (r⁻¹) ^ 2 * A r (f r) (g r)
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

end PoincareConjecture.M14
