import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapBoundaryAnchorOutside
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapBoundaryEntryProducer
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceBalancedChainAssembly

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

private theorem entry_below_graph_of_start_outside
    (N W : EpsilonNeck g) {γ : ℝ → M} {s t : ℝ}
    (hst : s < t) (hγ : ContinuousOn γ (Icc s t))
    (hstart : γ s ∉ W.carrier) (hWt : γ t ∈ W.carrier)
    (hNedge : MapsTo γ (Ico s t) N.carrier)
    (hoverlap : N.carrier ∩ W.carrier ⊆
      N.region (-(N.epsilon⁻¹ / 2)) N.epsilon⁻¹ ∩
        W.region (-W.epsilon⁻¹) (W.epsilon⁻¹ / 2))
    {f : UnitTwoSphere → ℝ} (hfb : ∀ p, |f p| < 7 * W.epsilon⁻¹ / 8) :
    ∃ a ∈ Ico s t, MapsTo γ (Icc a t) W.carrier ∧
      neckGraphHeight W f (γ a) < 0 := by
  obtain ⟨u, hu, hufront⟩ := ContinuousOn.exists_frontier_crossing_before
    (C := W.carrierᶜ) W.carrier_open.isClosed_compl hγ hst.le
    (show γ s ∈ W.carrierᶜ from hstart)
    (show γ t ∉ W.carrierᶜ from fun h => h hWt)
  have hufrontW : γ u ∈ frontier W.carrier := by
    simpa only [frontier_compl] using hufront
  let K : Set ℝ := Icc s t ∩ γ ⁻¹' frontier W.carrier
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset
    (hγ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_frontier)
    inter_subset_left
  obtain ⟨u', hu'K, hgreatest⟩ := hK.exists_isGreatest
    ⟨u, ⟨hu.1, hu.2.le⟩, hufrontW⟩
  have hufront' : γ u' ∈ frontier W.carrier := hu'K.2
  have hu't : u' < t := lt_of_le_of_ne hu'K.1.2 (by
    intro heq
    subst u'
    exact (W.carrier_open.frontier_eq ▸ hufront').2 hWt)
  have hu' : u' ∈ Ico s t := ⟨hu'K.1.1, hu't⟩
  have hafter : MapsTo γ (Ioo u' t) W.carrier := by
    intro r hr
    by_contra hrout
    have hγrt : ContinuousOn γ (Icc r t) :=
      hγ.mono (Icc_subset_Icc (hu'.1.trans hr.1.le) le_rfl)
    obtain ⟨q, hq, hqfront⟩ := ContinuousOn.exists_frontier_crossing_before
      (C := W.carrierᶜ) W.carrier_open.isClosed_compl hγrt hr.2.le
      (show γ r ∈ W.carrierᶜ from hrout)
      (show γ t ∉ W.carrierᶜ from fun h => h hWt)
    have hqfrontW : γ q ∈ frontier W.carrier := by
      simpa only [frontier_compl] using hqfront
    have hsq : s ≤ q := hu'.1.trans (le_of_lt (lt_of_lt_of_le hr.1 hq.1))
    have hqK : q ∈ K := ⟨⟨hsq, hq.2.le⟩, hqfrontW⟩
    have hqu : q ≤ u' := hgreatest hqK
    exact (not_le_of_gt (lt_of_lt_of_le hr.1 hq.1)) hqu
  have hlow : ∃ r ∈ Ioo u' t,
      (W.coordinate_inverse (γ r)).2 < -(7 * W.epsilon⁻¹ / 8) := by
    by_contra hnone
    have hbound (r : ℝ) (hr : r ∈ Ioo u' t) :
        -(7 * W.epsilon⁻¹ / 8) ≤ (W.coordinate_inverse (γ r)).2 := by
      by_contra hbad
      exact hnone ⟨r, hr, lt_of_not_ge hbad⟩
    have hslab : MapsTo γ (Ioo u' t)
        (W.coordinate_map ''
          (univ ×ˢ Icc (-(7 * W.epsilon⁻¹ / 8)) (W.epsilon⁻¹ / 2))) := by
      intro r hr
      have hrN : γ r ∈ N.carrier := hNedge ⟨hu'.1.trans hr.1.le, hr.2⟩
      have hrW : γ r ∈ W.carrier := hafter hr
      have hupper := (hoverlap ⟨hrN, hrW⟩).2.2.2
      exact ⟨W.coordinate_inverse (γ r),
        ⟨mem_univ _, hbound r hr, hupper.le⟩,
        W.coordinate_map_coordinate_inverse hrW⟩
    have hγclosure : ContinuousOn γ (closure (Ioo u' t)) := by
      rw [closure_Ioo hu'.2.ne]
      exact hγ.mono (Icc_subset_Icc hu'.1 le_rfl)
    have hslabclosure := hslab.closure_of_continuousOn hγclosure
    have huclosure : γ u' ∈ closure
        (W.coordinate_map ''
          (univ ×ˢ Icc (-(7 * W.epsilon⁻¹ / 8)) (W.epsilon⁻¹ / 2))) := by
      apply hslabclosure
      rw [closure_Ioo hu'.2.ne]
      exact left_mem_Icc.mpr hu'.2.le
    have hleft : -W.epsilon⁻¹ < -(7 * W.epsilon⁻¹ / 8) := by
      have hA : 0 < W.epsilon⁻¹ := inv_pos.mpr W.epsilon_pos
      linarith
    have hright : W.epsilon⁻¹ / 2 < W.epsilon⁻¹ := by
      have hA : 0 < W.epsilon⁻¹ := inv_pos.mpr W.epsilon_pos
      linarith
    have hclosed : IsClosed
        (W.coordinate_map ''
          (univ ×ˢ Icc (-(7 * W.epsilon⁻¹ / 8)) (W.epsilon⁻¹ / 2))) :=
      (W.isCompact_coordinate_slab hleft hright).isClosed
    have huW := W.coordinate_slab_subset_carrier_m28 hleft hright
      (hclosed.closure_subset huclosure)
    exact (W.carrier_open.frontier_eq ▸ hufront').2 huW
  obtain ⟨a, ha, haxis⟩ := hlow
  have hmap : MapsTo γ (Icc a t) W.carrier := by
    intro r hr
    by_cases hrt : r = t
    · simpa only [hrt] using hWt
    · exact hafter ⟨lt_of_lt_of_le ha.1 hr.1, lt_of_le_of_ne hr.2 hrt⟩
  refine ⟨a, ⟨hu'.1.trans ha.1.le, ha.2⟩, hmap, ?_⟩
  have hfa := abs_lt.mp (hfb (W.coordinate_inverse (γ a)).1)
  change (W.coordinate_inverse (γ a)).2 -
    f (W.coordinate_inverse (γ a)).1 < 0
  linarith only [haxis, hfa.1]

theorem SourceEdgeCommonOrientationPacket.exists_anchored_entry_below_cap_graph
    {N P W : EpsilonNeck g} {γ : ℝ → M} {tN tW epsilon : ℝ}
    (H : SourceEdgeCommonOrientationPacket N P W (γ := γ) tN tW)
    (J : SourceEdgePacket N W epsilon)
    (hε : N.epsilon ≤ 1 / 1000) {U : Set M} (hWU : W.carrier ⊆ U)
    {a b t₁ : ℝ} (ha₁ : a ≤ t₁) (h₁N : t₁ < tN)
    (hNW : tN < tW) (hWb : tW ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hfinite : g.pathELength γ a b ≠ ⊤)
    (hmin : g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b))
    (hanchor : g.pathELength γ t₁ tN =
      ENNReal.ofReal ((0.3 : ℝ) * N.scale * N.epsilon⁻¹))
    {f : UnitTwoSphere → ℝ} (hfb : ∀ p, |f p| < 7 * W.epsilon⁻¹ / 8) :
    MapsTo γ (Icc t₁ tN) N.carrier ∧ γ t₁ ∉ W.carrier ∧
      ∃ v ∈ Ico t₁ tW, MapsTo γ (Icc v tW) W.carrier ∧
        neckGraphHeight W f (γ v) < 0 := by
  obtain ⟨hprefix, hout⟩ := H.anchor_prefix_mem_and_not_mem_successor
    hε hWU ha₁ h₁N hNW hWb hγ hγU hfinite hmin hanchor
  refine ⟨hprefix, hout, ?_⟩
  have hNedge : MapsTo γ (Ico t₁ tW) N.carrier := by
    intro t ht
    by_cases htN : t ≤ tN
    · exact hprefix ⟨ht.1, htN⟩
    · exact H.edge ⟨(lt_of_not_ge htN).le, ht.2⟩
  have hWt : γ tW ∈ W.carrier := by
    rw [H.center_Q]
    exact W.central_sphere_subset W.center_on_central_sphere
  apply entry_below_graph_of_start_outside N W (h₁N.trans hNW)
    (hγ.continuousOn.mono (Icc_subset_Icc ha₁ hWb)) hout hWt hNedge _ hfb
  simpa only [J.epsilon_N, J.epsilon_Q, neg_div] using
    J.overlap_within_three_quarters

end PoincareConjecture.M28
