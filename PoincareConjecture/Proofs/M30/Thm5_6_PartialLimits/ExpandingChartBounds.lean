import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.ExpandingWindowInput
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Coordinates.Bounds
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Eventual










set_option autoImplicit false

open Set Filter Metric Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 100000 in





theorem referenceNormalChartCoefficients_on_expanding_time_domains
    {n : ℕ} {s' s : ℝ}
    (Href : PointedRicciFlowCompactnessHypotheses n s' s)
    (hShi : LocalCurvatureDerivativeEstimates.{0})
    {J : ℕ → Set ℝ}
    (Fseq : ∀ k, RicciFlow n (Href.sequence.carrier k).carrier (J k))
    (hmetric : ∀ k, (Fseq k).metric = (Href.sequence.flow k).flow.metric)
    {W : Set ℝ} (hW : IsOpen W) (hWord : W.OrdConnected) (hzero : (0 : ℝ) ∈ W)
    (htime : ∀ a b : ℝ, Icc a b ⊆ W → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (hcurv : ∀ a b : ℝ, Icc a b ⊆ W →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
        ∀ t ∈ Icc a b, ∀ x : (Href.sequence.carrier k).carrier,
          ((Fseq k).connection t).curvatureTensorNorm x ≤ C)
    {R ρ a b : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k →
      NormalChartCover (Href.sequence.flow k).flow.metric
        (Href.sequence.flow k).base s' s ((j : ℝ) + 1)
        (R j) (ρ j) (a j) (b j) (N j))
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, 2 * ρ j < R j)
    (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j) :
    ∀ i : ℕ,
      let raw := fun k (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
        ((Href.sequence.flow k).flow.metric z.1).pullbackCoefficients
          ((cover k (min (Nat.unpair i).1 k) (min_le_right _ _)).chart
            ⟨(Nat.unpair i).2 % (N (min (Nat.unpair i).1 k) + 1),
              Nat.mod_lt _ (Nat.succ_pos _)⟩) z.2
      LocallyEventuallyContDiff
          (W ×ˢ ball (0 : EuclideanSpace ℝ (Fin n)) (ρ (Nat.unpair i).1)) raw ∧
      (∀ K : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact K →
        K ⊆ W ×ˢ ball 0 (ρ (Nat.unpair i).1) → ∀ d : ℕ, ∃ B : ℝ,
          ∀ᶠ k in atTop, ∀ z ∈ K, ‖iteratedFDeriv ℝ d (raw k) z‖ ≤ B) ∧
      (∀ t ∈ W, ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
        ∀ x ∈ ball 0 (ρ (Nat.unpair i).1), ∀ v,
          c * ‖v‖ ^ 2 ≤ raw k (t, x) v v) := by
  classical
  have hwindow (I : Set ℝ) (hI : IsCompact I) (hIW : I ⊆ W) :
      ∃ l r : ℝ, (l < 0 ∧ 0 < r) ∧ Icc l r ⊆ W ∧ I ⊆ Ioo l r := by
    obtain ⟨m, hm⟩ := (hI.insert 0).exists_isLeast (insert_nonempty 0 I)
    obtain ⟨M, hM⟩ := (hI.insert 0).exists_isGreatest (insert_nonempty 0 I)
    have hmW : m ∈ W := by
      rcases hm.1 with rfl | hmI
      · exact hzero
      · exact hIW hmI
    have hMW : M ∈ W := by
      rcases hM.1 with rfl | hMI
      · exact hzero
      · exact hIW hMI
    obtain ⟨l, l', _, hlh, hlW⟩ :=
      exists_Icc_mem_subset_of_mem_nhds (hW.mem_nhds hmW)
    obtain ⟨r', r, _, hrh, hrW⟩ :=
      exists_Icc_mem_subset_of_mem_nhds (hW.mem_nhds hMW)
    have hl : m ∈ Ioo l l' := Icc_mem_nhds_iff.mp hlh
    have hr : M ∈ Ioo r' r := Icc_mem_nhds_iff.mp hrh
    refine ⟨l, r, ⟨hl.1.trans_le (hm.2 (mem_insert 0 I)),
      (hM.2 (mem_insert 0 I)).trans_lt hr.2⟩,
      hWord.out (hlW ⟨le_rfl, (hl.1.trans hl.2).le⟩)
        (hrW ⟨(hr.1.trans hr.2).le, le_rfl⟩), ?_⟩
    intro t ht
    exact ⟨hl.1.trans_le (hm.2 (mem_insert_of_mem 0 ht)),
      (hM.2 (mem_insert_of_mem 0 ht)).trans_lt hr.2⟩
  have hwide {l r : ℝ} (hlr : l < 0 ∧ 0 < r) (hIW : Icc l r ⊆ W) :
      ∃ (q : ℕ) (hsub : ∀ k, Ioo l r ⊆ J (k + q)),
        ∃ H : PointedRicciFlowCompactnessHypotheses n l r,
          H.sequence = sourceWindowSequence Href.sequence.carrier Fseq
            (fun k => (Href.sequence.flow k).base) q hsub (hlr.1.trans hlr.2) := by
    obtain ⟨C, hC, hbound⟩ := hcurv l r hIW
    apply exists_expanding_source_window_compactness Href Fseq
      (fun k => congrFun (hmetric k) 0) hlr (htime l r hIW)
    exact ⟨C, hC, hbound.mono (fun k hk t ht x => hk t ⟨ht.1.le, ht.2.le⟩ x)⟩
  have hwideMetric {l r : ℝ} (q : ℕ)
      (hsub : ∀ k, Ioo l r ⊆ J (k + q)) (hlr : l < r) (k : ℕ) :
      ((sourceWindowSequence Href.sequence.carrier Fseq
        (fun k => (Href.sequence.flow k).base) q hsub hlr).flow k).metricAt =
        (Href.sequence.flow (k + q)).flow.metric := hmetric (k + q)
  have unshift (q : ℕ) (P : ℕ → Prop)
      (hP : ∀ᶠ k in atTop, P (k + q)) : ∀ᶠ k in atTop, P k := by
    have hmap : ∀ᶠ k in Filter.map (fun k : ℕ => k + q) atTop, P k :=
      Filter.eventually_map.mpr hP
    simpa only [Filter.map_add_atTop_eq_nat] using hmap
  intro i
  let j := (Nat.unpair i).1
  let index (l : ℕ) : Fin (N l + 1) :=
    ⟨(Nat.unpair i).2 % (N l + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  let rawStage := fun k l (hlk : l ≤ k) (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
    ((Href.sequence.flow k).flow.metric z.1).pullbackCoefficients
      ((cover k l hlk).chart (index l)) z.2
  let raw := fun k => rawStage k (min j k) (min_le_right _ _)
  have hraw (k : ℕ) (hk : j ≤ k) : raw k = rawStage k j hk := by
    funext z
    simp only [raw, min_eq_left hk]
  change LocallyEventuallyContDiff (W ×ˢ ball 0 (ρ j)) raw ∧
    (∀ K : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact K →
      K ⊆ W ×ˢ ball 0 (ρ j) → ∀ d : ℕ, ∃ B : ℝ,
        ∀ᶠ k in atTop, ∀ z ∈ K, ‖iteratedFDeriv ℝ d (raw k) z‖ ≤ B) ∧
    (∀ t ∈ W, ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∀ x ∈ ball 0 (ρ j), ∀ v, c * ‖v‖ ^ 2 ≤ raw k (t, x) v v)
  refine ⟨?_, ?_, ?_⟩
  · intro K hK hKW
    have hIW : Prod.fst '' K ⊆ W := by
      rintro t ⟨z, hz, rfl⟩
      exact (hKW hz).1
    obtain ⟨l, r, hlr, hlrW, hIlr⟩ :=
      hwindow (Prod.fst '' K) (hK.image continuous_fst) hIW
    obtain ⟨q, hsub, H, hH⟩ := hwide hlr hlrW
    have hsmooth := H.referenceNormalChartCover_contDiffOn
      (S' := s') (S := s) (A := (j : ℝ) + 1) (R := R j) (ρ := ρ j)
      (a := a j) (b := b j) (N := N j)
    rw [hH] at hsmooth
    apply unshift q
    filter_upwards [(Filter.tendsto_add_atTop_nat q).eventually
      (eventually_ge_atTop j)] with k hk
    refine ⟨Ioo l r ×ˢ ball 0 (R j), isOpen_Ioo.prod isOpen_ball, ?_, ?_⟩
    · intro z hz
      exact ⟨hIlr (mem_image_of_mem Prod.fst hz),
        ball_subset_ball (show ρ j ≤ R j by linarith [hρ j, hρR j]) (hKW hz).2⟩
    · have hsmoothk := hsmooth k
      rw [hwideMetric] at hsmoothk
      rw [hraw (k + q) hk]
      exact hsmoothk (cover (k + q) j hk) (index j)
  · intro K hK hKW d
    have hIW : Prod.fst '' K ⊆ W := by
      rintro t ⟨z, hz, rfl⟩
      exact (hKW hz).1
    obtain ⟨l, r, hlr, hlrW, hIlr⟩ :=
      hwindow (Prod.fst '' K) (hK.image continuous_fst) hIW
    obtain ⟨q, hsub, H, hH⟩ := hwide hlr hlrW
    obtain ⟨B, _, hbound⟩ := H.eventually_referenceNormalChartCover_spacetime_jet_bound
      hShi Href.time_bounds (hK.image continuous_fst) hIlr (N := N j)
      (show 0 < (j : ℝ) + 1 by positivity) (hρ j) (hρR j) (ha j) (hb j) d
    rw [hH] at hbound
    refine ⟨B, unshift q _ ?_⟩
    filter_upwards [hbound, (Filter.tendsto_add_atTop_nat q).eventually
      (eventually_ge_atTop j)] with k hk hkj z hz
    rw [hwideMetric] at hk
    have h := hk (cover (k + q) j hkj) (index j) z.1
      (mem_image_of_mem Prod.fst hz) z.2 (ball_subset_closedBall (hKW hz).2)
    rw [hraw (k + q) hkj]
    exact h
  · intro t ht
    obtain ⟨l, r, hlr, hlrW, htlr⟩ :=
      hwindow {t} isCompact_singleton (singleton_subset_iff.mpr ht)
    obtain ⟨q, hsub, H, hH⟩ := hwide hlr hlrW
    obtain ⟨c, _, hc, _, hbound⟩ := H.eventually_referenceNormalChartCover_ellipticity
      Href.time_bounds (N := N j) (show 0 < (j : ℝ) + 1 by positivity)
      (hρ j) (hρR j) (ha j) (hb j)
    rw [hH] at hbound
    refine ⟨c, hc, unshift q _ ?_⟩
    filter_upwards [hbound, (Filter.tendsto_add_atTop_nat q).eventually
      (eventually_ge_atTop j)] with k hk hkj x hx v
    rw [hwideMetric] at hk
    have hx' : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * ρ j) :=
      closedBall_subset_closedBall (by linarith [hρ j]) (ball_subset_closedBall hx)
    have h := (hk (cover (k + q) j hkj) (index j) t (htlr (mem_singleton t)) x hx' v).1
    rw [hraw (k + q) hkj]
    exact h

end PoincareConjecture.M30
