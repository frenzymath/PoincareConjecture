import PoincareConjecture.Proofs.M15.Lemma8_7_SpatialLift
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I K : SpacetimeInterval}
  (G : GeneralizedLGeometryTransport n X time I)
  (D : SmoothSpacetimeInterval K)
  {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
  [IsManifold (𝓡 n) ∞ C]
  (e : CompatibleSpacetimeCylinder G.spacetime D C)
  (g : SpacetimeCylinderMetric e)

include g

theorem compatibleCylinder_spatialOpen_image_mem_nhdsWithin_timeDomain
    (q : D.Point × C) {U : Set C} (hU : IsOpen U) (hq : q.2 ∈ U) :
    e.toSpacetime '' (Set.univ ×ˢ U) ∈
      nhdsWithin (e.toSpacetime q)
        {p : G.Point | G.spacetime.timeFunction p ∈ K.domain} := by
  obtain ⟨O, hO, hOU⟩ := e.embedding.isInducing.isOpen_iff.mp (isOpen_univ.prod hU)
  have hqO : e.toSpacetime q ∈ O := by
    change q ∈ e.toSpacetime ⁻¹' O
    rw [hOU]
    exact ⟨mem_univ _, hq⟩
  have hn := compatibleCylinder_range_mem_nhdsWithin_timeDomain G D e g q
  have ho : O ∈ 𝓝[{p : G.Point | G.spacetime.timeFunction p ∈ K.domain}]
      (e.toSpacetime q) := mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hqO)
  filter_upwards [hn, ho] with p hp hpO
  obtain ⟨z, rfl⟩ := hp
  refine ⟨z, ?_, rfl⟩
  rw [← hOU]
  exact hpO

theorem compatibleCylinder_lift_of_compact_prefix_trap
    (hK : IsCompact K.domain)
    {U A : Set C} (hU : IsOpen U) (hA : IsCompact A) (hAU : A ⊆ U)
    (q : D.Point × C) (hq : q.2 ∈ A)
    {S : ℝ} (hS : 0 ≤ S) (gamma : ℝ → G.Point)
    (hgamma : ContMDiffOn 𝓘(ℝ) (spacetimeModel n) ∞ gamma (Set.Icc 0 S))
    (hzero : gamma 0 = e.toSpacetime q)
    (htime : ∀ s ∈ Set.Icc 0 S,
      G.spacetime.timeFunction (gamma s) ∈ K.domain)
    (htrap : ∀ b ∈ Set.Ioc 0 S,
      (∀ s ∈ Set.Icc 0 b, gamma s ∈ e.toSpacetime '' (Set.univ ×ˢ U)) →
      gamma b ∈ e.toSpacetime '' (Set.univ ×ˢ A)) :
    ∃ L : ℝ → D.Point × C,
      L 0 = q ∧
      ContMDiffOn 𝓘(ℝ) (spacetimeModel n) ∞ L (Set.Icc 0 S) ∧
      ∀ s ∈ Set.Icc 0 S,
        e.toSpacetime (L s) = gamma s ∧ (L s).2 ∈ A := by
  let : CompactSpace D.Point := isCompact_iff_compactSpace.mp hK
  have hQ : IsCompact (e.toSpacetime '' (univ ×ˢ A)) :=
    (isCompact_univ.prod hA).image e.embedding.continuous
  let H := gamma ⁻¹' (e.toSpacetime '' (univ ×ˢ A))
  have hH : IsClosed (H ∩ Icc 0 S) := by
    simpa only [H, inter_comm] using
      hgamma.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hQ.isClosed
  have h0 : (0 : ℝ) ∈ H := ⟨q, ⟨mem_univ _, hq⟩, hzero.symm⟩
  have hAll : Icc 0 S ⊆ H := by
    apply hH.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset h0
    intro t ht hprefix
    obtain ⟨qt, hqt, heqt⟩ := hprefix ⟨ht.1, le_rfl⟩
    have hn := compatibleCylinder_spatialOpen_image_mem_nhdsWithin_timeDomain
      G D e g qt hU (hAU hqt.2)
    rw [heqt] at hn
    have hpre : gamma ⁻¹' (e.toSpacetime '' (univ ×ˢ U)) ∈ 𝓝[Icc 0 S] t :=
      ((hgamma t ⟨ht.1, ht.2.le⟩).continuousWithinAt.tendsto_nhdsWithin
        (t := {p : G.Point | G.spacetime.timeFunction p ∈ K.domain})
        (fun s hs => htime s hs)) hn
    obtain ⟨O, hO, hOI⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
    obtain ⟨delta, hdelta, hdeltaO⟩ := Metric.mem_nhds_iff.mp hO
    let m := min S (t + delta / 2)
    have htm : t < m := lt_min ht.2 (by linarith)
    apply (mem_nhdsGT_iff_exists_Ioo_subset' ht.2).mpr
    refine ⟨m, htm, ?_⟩
    intro b hb
    have hbS : b ≤ S := hb.2.le.trans (min_le_left _ _)
    apply htrap b ⟨lt_of_le_of_lt ht.1 hb.1, hbS⟩
    intro s hs
    by_cases hst : s ≤ t
    · obtain ⟨qs, hqs, heqs⟩ := hprefix ⟨hs.1, hst⟩
      exact ⟨qs, ⟨mem_univ _, hAU hqs.2⟩, heqs⟩
    · have hts : t < s := lt_of_not_ge hst
      apply hOI
      refine ⟨hdeltaO ?_, ⟨hs.1, hs.2.trans hbS⟩⟩
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr hts)]
      have hbm : b < t + delta / 2 := hb.2.trans_le (min_le_right _ _)
      linarith [hs.2]
  let : Nonempty (D.Point × C) := ⟨q⟩
  let L := fun s => Function.invFun e.toSpacetime (gamma s)
  have hL (s : ℝ) (hs : s ∈ Icc 0 S) : e.toSpacetime (L s) = gamma s := by
    apply Function.invFun_eq
    obtain ⟨z, _, hz⟩ := hAll hs
    exact ⟨z, hz⟩
  refine ⟨L, ?_, compatibleCylinder_lift_contMDiffOn G D e g hgamma L hL, ?_⟩
  · apply e.embedding.injective
    exact (hL 0 ⟨le_rfl, hS⟩).trans hzero
  · intro s hs
    refine ⟨hL s hs, ?_⟩
    obtain ⟨z, hz, hez⟩ := hAll hs
    have hLz : L s = z := e.embedding.injective ((hL s hs).trans hez.symm)
    rw [hLz]
    exact hz.2

end PoincareConjecture.Proofs.M15
