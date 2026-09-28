import PoincareConjecture.Proofs.M15.Lemma8_7_SpatialInverse










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.Proofs.M15




theorem compatibleCylinder_spatial_lift_contMDiffOn
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    {time : X → ℝ} {I K : SpacetimeInterval}
    (G : GeneralizedLGeometryTransport n X time I)
    (D : SmoothSpacetimeInterval K)
    {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C]
    (e : CompatibleSpacetimeCylinder G.spacetime D C)
    (g : SpacetimeCylinderMetric e)
    {J : Set ℝ} {gamma : ℝ → G.Point}
    (hgamma : ContMDiffOn 𝓘(ℝ) (spacetimeModel n) ∞ gamma J)
    (L : ℝ → D.Point × C)
    (hL : ∀ s ∈ J, e.toSpacetime (L s) = gamma s) :
    ContMDiffOn 𝓘(ℝ) (𝓡 n) ∞ (fun s => (L s).2) J := by
  intro s hs
  obtain ⟨O, hO, hpO, k, hk, hrecover⟩ :=
    compatibleCylinder_exists_local_spatial_inverse G D e g (L s)
  rw [hL s hs] at hpO
  have hcomp := ((hk _ hpO).contMDiffAt (hO.mem_nhds hpO)).comp_contMDiffWithinAt s
    (hgamma s hs)
  apply hcomp.congr_of_eventuallyEq_of_mem _ hs
  have hn : ∀ᶠ t in 𝓝[J] s, gamma t ∈ O :=
    (hgamma s hs).continuousWithinAt (hO.mem_nhds hpO)
  filter_upwards [hn, self_mem_nhdsWithin] with t htO htJ
  change (L t).2 = k (gamma t)
  rw [← hL t htJ]
  exact (hrecover (L t) (by rwa [hL t htJ])).symm




theorem compatibleCylinder_exists_initial_lift
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    {time : X → ℝ} {I K : SpacetimeInterval}
    (G : GeneralizedLGeometryTransport n X time I)
    (D : SmoothSpacetimeInterval K)
    {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C]
    (e : CompatibleSpacetimeCylinder G.spacetime D C)
    (g : SpacetimeCylinderMetric e) (q : D.Point × C)
    {S : ℝ} (hS : 0 < S) (gamma : ℝ → G.Point)
    (hgamma : ContMDiffOn 𝓘(ℝ) (spacetimeModel n) ∞ gamma (Set.Icc 0 S))
    (hzero : gamma 0 = e.toSpacetime q)
    (htime : ∀ s ∈ Set.Icc 0 S,
      G.spacetime.timeFunction (gamma s) ∈ K.domain) :
    ∃ d : ℝ, 0 < d ∧ d ≤ S ∧ ∃ L : ℝ → D.Point × C,
      L 0 = q ∧ ContinuousOn L (Set.Icc 0 d) ∧
      ContMDiffOn 𝓘(ℝ) (𝓡 n) ∞ (fun s => (L s).2) (Set.Icc 0 d) ∧
      ∀ s ∈ Set.Icc 0 d, e.toSpacetime (L s) = gamma s := by
  have h0 : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS.le⟩
  have hN := compatibleCylinder_range_mem_nhdsWithin_timeDomain G D e g q
  rw [← hzero] at hN
  have hpre : gamma ⁻¹' range e.toSpacetime ∈ 𝓝[Icc 0 S] (0 : ℝ) :=
    ((hgamma 0 h0).continuousWithinAt.tendsto_nhdsWithin
      (t := {p : G.Point | G.spacetime.timeFunction p ∈ K.domain})
      (fun s hs => htime s hs)) hN
  obtain ⟨U, hU, hUI⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
  obtain ⟨eta, heta, hetaU⟩ := Metric.mem_nhds_iff.mp hU
  let d := min S (eta / 2)
  have hd : 0 < d := lt_min hS (half_pos heta)
  have hdS : d ≤ S := min_le_left _ _
  have hdeta : d < eta := (min_le_right _ _).trans_lt (half_lt_self heta)
  have hsub : Icc 0 d ⊆ Icc 0 S := fun _ hs => ⟨hs.1, hs.2.trans hdS⟩
  have hRange (s : ℝ) (hs : s ∈ Icc 0 d) : gamma s ∈ range e.toSpacetime := by
    apply hUI
    refine ⟨hetaU ?_, hsub hs⟩
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
      using hs.2.trans_lt hdeta
  let : Nonempty (D.Point × C) := ⟨q⟩
  let L := fun s => Function.invFun e.toSpacetime (gamma s)
  have hL (s : ℝ) (hs : s ∈ Icc 0 d) : e.toSpacetime (L s) = gamma s :=
    Function.invFun_eq (hRange s hs)
  refine ⟨d, hd, hdS, L, ?_, ?_, ?_, hL⟩
  · apply e.embedding.injective
    exact (hL 0 ⟨le_rfl, hd.le⟩).trans hzero
  · apply e.embedding.isInducing.continuousOn_iff.mpr
    exact (hgamma.continuousOn.mono hsub).congr hL
  · exact compatibleCylinder_spatial_lift_contMDiffOn G D e g (hgamma.mono hsub) L hL




theorem compatibleCylinder_lift_contMDiffOn
    {n : ℕ} {X : Type u} [TopologicalSpace X]
    {time : X → ℝ} {I K : SpacetimeInterval}
    (G : GeneralizedLGeometryTransport n X time I)
    (D : SmoothSpacetimeInterval K)
    {C : Type v} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
    [IsManifold (𝓡 n) ∞ C]
    (e : CompatibleSpacetimeCylinder G.spacetime D C)
    (g : SpacetimeCylinderMetric e)
    {J : Set ℝ} {gamma : ℝ → G.Point}
    (hgamma : ContMDiffOn 𝓘(ℝ) (spacetimeModel n) ∞ gamma J)
    (L : ℝ → D.Point × C)
    (hL : ∀ s ∈ J, e.toSpacetime (L s) = gamma s) :
    ContMDiffOn 𝓘(ℝ) (spacetimeModel n) ∞ L J := by
  have htime : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞
      (G.spacetime.timeFunction ∘ gamma) J :=
    (show ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ G.spacetime.timeFunction from
      G.spacetime.time_smooth).comp_contMDiffOn hgamma
  have hvalid : MapsTo (G.spacetime.timeFunction ∘ gamma) J K.domain := by
    intro s hs
    change G.spacetime.timeFunction (gamma s) ∈ K.domain
    rw [← hL s hs, e.time_eq]
    exact (L s).1.property
  have hfirst := D.realParam_smoothOn.comp htime hvalid
  have hspatial := compatibleCylinder_spatial_lift_contMDiffOn G D e g hgamma L hL
  apply (hfirst.prodMk hspatial).congr
  intro s hs
  have hval : D.realParam (G.spacetime.timeFunction (gamma s)) = (L s).1 := by
    rw [← hL s hs, e.time_eq, D.realParam_coe]
  change L s = (D.realParam (G.spacetime.timeFunction (gamma s)), (L s).2)
  rw [hval]

end PoincareConjecture.Proofs.M15
