import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapBoundaryPathCrossing
import PoincareConjecture.Proofs.M28.Mathlib.FrontierCrossing













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}





theorem exists_predecessor_entry_below_cap_graph
    (P W : EpsilonNeck g)
    {γ : ℝ → M} {s t b : ℝ}
    (hst : s < t) (htb : t < b)
    (hγ : ContinuousOn γ (Icc s b))
    (hγs : γ s = P.center)
    (hPout : P.center ∉ W.carrier)
    (hγt : γ t = W.center)
    (hPedge : MapsTo γ (Ico s t) P.carrier)
    (hWfinal : MapsTo γ (Icc t b) W.carrier)
    (hoverlap : P.carrier ∩ W.carrier ⊆
      P.region (-(P.epsilon⁻¹ / 2)) P.epsilon⁻¹ ∩
        W.region (-W.epsilon⁻¹) (W.epsilon⁻¹ / 2))
    {f : UnitTwoSphere → ℝ}
    (hfb : ∀ p, |f p| < 7 * W.epsilon⁻¹ / 8) :
    ∃ a ∈ Ico s t,
      MapsTo γ (Icc a t) W.carrier ∧
        neckGraphHeight W f (γ a) < 0 := by
  have hγst : ContinuousOn γ (Icc s t) :=
    hγ.mono (Icc_subset_Icc le_rfl htb.le)
  have hstart : γ s ∉ W.carrier := by
    rw [hγs]
    exact hPout
  have hWcenter : W.center ∈ W.carrier := by
    simpa [hγt] using (hWfinal ⟨le_rfl, htb.le⟩)
  have hWt : γ t ∈ W.carrier := by
    simpa [hγt] using hWcenter
  obtain ⟨u, hu, hufront⟩ :=
    ContinuousOn.exists_frontier_crossing_before
      (C := W.carrierᶜ) W.carrier_open.isClosed_compl hγst hst.le
      (show γ s ∈ W.carrierᶜ from hstart)
      (show γ t ∉ W.carrierᶜ from fun h => h hWt)
  have hufrontW : γ u ∈ frontier W.carrier := by
    simpa only [frontier_compl] using hufront
  let K : Set ℝ := Icc s t ∩ γ ⁻¹' frontier W.carrier
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset
    (hγst.preimage_isClosed_of_isClosed isClosed_Icc isClosed_frontier)
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
      hγ.mono (Icc_subset_Icc (hu'.1.trans hr.1.le) htb.le)
    obtain ⟨q, hq, hqfront⟩ :=
      ContinuousOn.exists_frontier_crossing_before
        (C := W.carrierᶜ) W.carrier_open.isClosed_compl hγrt hr.2.le
        (show γ r ∈ W.carrierᶜ from hrout)
        (show γ t ∉ W.carrierᶜ from fun h => h hWt)
    have hqfrontW : γ q ∈ frontier W.carrier := by
      simpa only [frontier_compl] using hqfront
    have hsq : s ≤ q := hu'.1.trans (le_of_lt (lt_of_lt_of_le hr.1 hq.1))
    have hqK : q ∈ K := by
      refine ⟨⟨hsq, hq.2.le⟩, hqfrontW⟩
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
          (univ ×ˢ Icc (-(7 * W.epsilon⁻¹ / 8))
            (W.epsilon⁻¹ / 2))) := by
      intro r hr
      have hrP : γ r ∈ P.carrier := hPedge
        ⟨hu'.1.trans hr.1.le, hr.2⟩
      have hrW : γ r ∈ W.carrier := hafter hr
      have hover := hoverlap ⟨hrP, hrW⟩
      have hWupper := hover.2.2
      refine ⟨W.coordinate_inverse (γ r), ?_,
        W.coordinate_map_coordinate_inverse hrW⟩
      refine ⟨mem_univ _, hbound r hr, hWupper.2.le⟩
    have hγclosure : ContinuousOn γ (closure (Ioo u' t)) := by
      rw [closure_Ioo hu'.2.ne]
      exact hγ.mono (Icc_subset_Icc hu'.1 htb.le)
    have hslabclosure := hslab.closure_of_continuousOn hγclosure
    have huclosure : γ u' ∈ closure
        (W.coordinate_map ''
          (univ ×ˢ Icc (-(7 * W.epsilon⁻¹ / 8))
            (W.epsilon⁻¹ / 2))) := by
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
          (univ ×ˢ Icc (-(7 * W.epsilon⁻¹ / 8))
            (W.epsilon⁻¹ / 2))) := by
      exact (W.isCompact_coordinate_slab hleft hright).isClosed
    have huSlab := hclosed.closure_subset huclosure
    have huW := W.coordinate_slab_subset_carrier_m28 hleft hright huSlab
    exact (W.carrier_open.frontier_eq ▸ hufront').2 huW
  obtain ⟨a, ha, haxis⟩ := hlow
  have haIco : a ∈ Ico s t :=
    ⟨hu'.1.trans ha.1.le, ha.2⟩
  have hmap : MapsTo γ (Icc a t) W.carrier := by
    intro r hr
    by_cases hrt : r = t
    · simpa only [hrt] using hWt
    · have hrt' : r < t := lt_of_le_of_ne hr.2 hrt
      exact hafter ⟨lt_of_lt_of_le ha.1 hr.1, hrt'⟩
  refine ⟨a, haIco, hmap, ?_⟩
  have hfa := abs_lt.mp (hfb (W.coordinate_inverse (γ a)).1)
  change (W.coordinate_inverse (γ a)).2 -
      f (W.coordinate_inverse (γ a)).1 < 0
  linarith [haxis, hfa.1]

end PoincareConjecture.M28
