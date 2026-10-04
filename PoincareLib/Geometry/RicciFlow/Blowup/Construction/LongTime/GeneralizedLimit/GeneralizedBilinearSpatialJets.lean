import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.GeneralizedLimit.GeneralizedScalarSpatialJets
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.LongTime.GeneralizedLimit.GeneralizedCoefficientLimit
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Analysis.UniformBilinearJets
import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Operator

/-!
# Actual bilinear spatial jets on generalized limits

The actual normalized metric coefficients retain all compact spatial jets
of the frozen generalized convergence, including the closed time endpoints.
Source: Morgan--Tian Definition 5.12, Proposition 5.14 and Theorem 11.8,
pp. 90--91 and 272; M30 `generalized-native-curvature-readout.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

/-- The actual normalized slice pullback on its recorded window, with a
total zero branch outside it (Definition 5.12, p. 90; Theorem 11.8, p. 272). -/
noncomputable def generalizedPullbackCoefficients
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (k : ℕ)
    (q : G.limit.carrier.carrier) (p : ℝ × EuclideanSpace ℝ (Fin 3)) :
    SpacetimeBounds.MetricCoefficient 3 := by
  classical
  exact if ht : p.1 ∈ Icc (-G.exhaustion.time k) 0 then
    (normalizedBlowupSliceMetric S (G.subsequence k) p.1).pullbackCoefficients
      (generalizedSliceHomeomorph G k p.1 ht ∘ (extChartAt (𝓡 3) q).symm) p.2
  else 0

/-- Every finite actual bilinear spatial jet converges uniformly on compact
spacetime tests with the original maps and windows (Definition 5.12 and
Proposition 5.14, pp. 90--91; Theorem 11.8, p. 272). -/
theorem tendstoUniformlyOn_generalized_bilinear_spatial_jets
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (q : G.limit.carrier.carrier)
    (r : ℕ) {K : Set (ℝ × EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKc : K ⊆ blowupMetricChartDomain G.limit q) :
    TendstoUniformlyOn
      (fun k p => iteratedFDeriv ℝ r
        (fun y => generalizedPullbackCoefficients G k q (p.1, y)) p.2)
      (fun p => iteratedFDeriv ℝ r
        ((G.limit.flow.metric p.1).pullbackCoefficients
          (extChartAt (𝓡 3) q).symm) p.2) atTop K := by
  let E := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let c := extChartAt (𝓡 3) q
  let f := fun k t x => generalizedPullbackCoefficients G k q (t, x)
  let g := fun t => (G.limit.flow.metric t).pullbackCoefficients c.symm
  have hc : ContinuousOn c.symm c.target := (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn
  have hmap : ContinuousOn (fun p : ℝ × E => c.symm p.2) K :=
    hc.comp continuousOn_snd (fun p hp => (hKc hp).2)
  obtain ⟨j, hj⟩ := exists_generalized_exhaustion_stage G (hK.image_of_continuousOn hmap)
  have hvalid : ∀ᶠ k in atTop, ∀ p ∈ K,
      p.1 ∈ Icc (-G.exhaustion.time k) 0 ∧ c.symm p.2 ∈ G.exhaustion.space k := by
    have htime := G.exhaustion.time_cofinal (Prod.fst '' K)
      (hK.image continuous_fst) (by rintro _ ⟨p, hp, rfl⟩; exact (hKc hp).1)
    filter_upwards [htime, eventually_ge_atTop j] with k hk hjk p hp
    exact ⟨hk (mem_image_of_mem _ hp),
      G.exhaustion.space_increasing hjk (hj (mem_image_of_mem _ hp))⟩
  have hchart (x : E) (hx : x ∈ c.target) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm x :=
    (contMDiffOn_extChartAt_symm q).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hx)
  have hf : ∀ᶠ k in atTop, ∀ p ∈ K, ContDiffAt ℝ ∞ (f k p.1) p.2 := by
    filter_upwards [hvalid] with k hk p hp
    have ht := (hk p hp).1
    have he := (generalizedSliceHomeomorph_contMDiffAt G k p.1 ht
      (hk p hp).2).comp p.2 (hchart p.2 (hKc hp).2)
    have H := RiemannianMetric.contDiffAt_pullbackCoefficients
      (normalizedBlowupSliceMetric S (G.subsequence k) p.1) he
    simpa only [f, generalizedPullbackCoefficients, dif_pos ht] using H
  have hg : ∀ p ∈ K, ContDiffAt ℝ ∞ (g p.1) p.2 := fun p hp =>
    (G.limit.flow.metric p.1).contDiffAt_pullbackCoefficients (hchart p.2 (hKc hp).2)
  apply tendstoUniformlyOn_bilinear_jets_of_scalar_entries
    (EuclideanSpace.basisFun (Fin 3) ℝ) r hf hg
  intro a b
  apply (tendstoUniformlyOn_generalized_scalar_spatial_jets G q r a b hK hKc).congr
  filter_upwards [hvalid] with k hk p hp
  let V := c.target ∩ c.symm ⁻¹' G.exhaustion.space k
  have hV : IsOpen V := hc.isOpen_inter_preimage
    (isOpen_extChartAt_target (I := 𝓡 3) q) (G.exhaustion.space_open k)
  have hpV : p.2 ∈ V := ⟨(hKc hp).2, (hk p hp).2⟩
  have ht := (hk p hp).1
  have heq : (fun y => blowupPullbackCoefficient (G.embedding k) q a b (p.1, y)) =ᶠ[𝓝 p.2]
      (fun y => f k p.1 y (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) := by
    filter_upwards [hV.mem_nhds hpV] with y hy
    simpa only [f, generalizedPullbackCoefficients, dif_pos ht] using
      (generalized_slice_coefficient_eq G k p.1 ht q hy.1 hy.2 a b).symm
  exact (heq.iteratedFDeriv ℝ r).self_of_nhds

end PoincareMT.M30
