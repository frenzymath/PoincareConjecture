import PoincareConjecture.Proofs.M30.Thm11_8.BackwardInterval
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.TerminalCompleteness
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.TimeTranslation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Window
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space

noncomputable def retainedBackwardBlowupLimit
    {s' s : ℝ} {T0 : ℝ≥0∞} {Jsrc : ℕ → Set ℝ}
    {S : PointedFlowSequence 3 s' s}
    (G : PointedGeometricConvergence S)
    (Fsrc : ∀ k, RicciFlow 3 (S.carrier k).carrier (Jsrc k))
    (F : RicciFlow 3 G.limitCarrier.carrier (blowupBackwardInterval T0))
    {t_ref : ℝ} (ht_ref : t_ref < 0)
    (ht_ref_mem : t_ref ∈ blowupBackwardInterval T0)
    (hcomplete : G.limitCarrier.metricComplete (F.metric t_ref))
    (hcurv : ∀ A : ℝ, 0 < A → ENNReal.ofReal A < T0 →
      ∃ B : ℝ, ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (-A) 0,
        ∀ x : (S.carrier k).carrier,
          ((Fsrc k).connection t).curvatureTensorNorm x ≤ B)
    (hnormalized : ∀ᶠ k : ℕ in atTop,
      ((Fsrc k).connection 0).scalarCurvature (S.flow k).base = 1)
    (hreadout : ∀ t ∈ blowupBackwardInterval T0,
      ∀ x : G.limitCarrier.carrier,
      Tendsto (fun k => ((Fsrc (G.subsequence k)).connection t).scalarCurvature
        (((G.embedding k).toFun (0, x)).2)) atTop
        (𝓝 ((F.connection t).scalarCurvature x)) ∧
      Tendsto (fun k => ((Fsrc (G.subsequence k)).connection t).curvatureTensorNorm
        (((G.embedding k).toFun (0, x)).2)) atTop
        (𝓝 ((F.connection t).curvatureTensorNorm x)) ∧
      (F.connection t).NonnegativeCurvatureOperator x) :
    BlowupLimitFlow.{0} (blowupBackwardInterval T0) := by
  have hbound (A : ℝ) (hA : 0 < A) (hAT : ENNReal.ofReal A < T0) :
      ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc (-A) 0,
        ∀ x : G.limitCarrier.carrier,
          (F.connection t).curvatureTensorNorm x ≤ K := by
    obtain ⟨B, hB⟩ := hcurv A hA hAT
    refine ⟨max B 0, le_max_right B 0, ?_⟩
    intro t ht x
    apply le_trans _ (le_max_left B 0)
    apply le_of_tendsto
      (hreadout t (closedSlab_subset_blowupBackwardInterval hAT ht) x).2.1
    filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually hB] with k hk
    exact hk t ht (((G.embedding k).toFun (0, x)).2)
  have hrefSlab : Icc t_ref 0 ⊆ blowupBackwardInterval T0 := by
    simpa only [neg_neg] using closedSlab_subset_blowupBackwardInterval ht_ref_mem.2
  have hzero : (0 : ℝ) ∈ blowupBackwardInterval T0 :=
    hrefSlab ⟨ht_ref.le, le_rfl⟩
  have hnegativeComplete (t : ℝ) (ht : t ∈ blowupBackwardInterval T0)
      (ht0 : t < 0) : G.limitCarrier.metricComplete (F.metric t) := by
    let O : Set ℝ := {z | ENNReal.ofReal (-z) < T0}
    have hO : IsOpen O :=
      isOpen_Iio.preimage (ENNReal.continuous_ofReal.comp continuous_neg)
    have hmO : min t_ref t ∈ O := by
      change ENNReal.ofReal (-(min t_ref t)) < T0
      rcases le_total t_ref t with h | h
      · rw [min_eq_left h]
        exact ht_ref_mem.2
      · rw [min_eq_right h]
        exact ht.2
    obtain ⟨l, hl, hlO⟩ := Filter.Eventually.exists_lt (hO.mem_nhds hmO)
    have hlref : l < t_ref := hl.trans_le (min_le_left t_ref t)
    have hlt : l < t := hl.trans_le (min_le_right t_ref t)
    have hl0 : l < 0 := hlref.trans ht_ref
    have hlT : ENNReal.ofReal (-l) < T0 := hlO
    let r : ℝ := max t_ref t / 2
    have hmax0 : max t_ref t < 0 := max_lt ht_ref ht0
    have hmaxr : max t_ref t < r := by dsimp only [r]; linarith
    have hr0 : r < 0 := by dsimp only [r]; linarith
    have hrefr : t_ref < r := (le_max_left t_ref t).trans_lt hmaxr
    have htr : t < r := (le_max_right t_ref t).trans_lt hmaxr
    let a : ℝ := l - t_ref
    let b : ℝ := r - t_ref
    have ha : a < 0 := by dsimp only [a]; linarith
    have hb : 0 < b := by dsimp only [b]; linarith
    have hab : a < b := ha.trans hb
    have hphysical (z : ℝ) (hz : z ∈ Ioo a b) : z + t_ref ∈ Icc l 0 := by
      constructor
      · dsimp only [a] at hz
        linarith [hz.1]
      · dsimp only [b] at hz
        linarith [hz.2]
    have hslab : Icc l 0 ⊆ blowupBackwardInterval T0 := by
      simpa only [neg_neg] using closedSlab_subset_blowupBackwardInterval hlT
    have hImage : (fun z : ℝ => z + t_ref) '' Ioo a b ⊆
        blowupBackwardInterval T0 := by
      rintro _ ⟨z, hz, rfl⟩
      exact hslab (hphysical z hz)
    have hNontrivial : (Ioo a b).Nontrivial := by
      refine ⟨(2 * a + b) / 3, ⟨?_, ?_⟩,
        (a + 2 * b) / 3, ⟨?_, ?_⟩, ?_⟩ <;> linarith
    let Fshift : RicciFlow 3 G.limitCarrier.carrier (Ioo a b) :=
      F.translate t_ref hImage ordConnected_Ioo hNontrivial
    let Bflow : BasedFlow 3 a b G.limitCarrier :=
      G.limitCarrier.basedWindow Fshift G.limitFlow.base (Subset.refl _) hab
    have hBmetric (z : ℝ) : Bflow.metricAt z = F.metric (z + t_ref) := rfl
    have hBcomplete : G.limitCarrier.metricComplete (Bflow.metricAt 0) := by
      rw [hBmetric, zero_add]
      exact hcomplete
    obtain ⟨K, hK, hKl⟩ := hbound (-l) (by linarith) hlT
    simp only [neg_neg] at hKl
    have hresult := Bflow.complete_interior_of_two_time_curvature_bound ⟨ha, hb⟩
      hBcomplete (fun _ _ => ⟨K, hK, by
        intro _ _ z hz x _
        change (F.connection (z + t_ref)).curvatureTensorNorm x ≤ K
        exact hKl (z + t_ref) (hphysical z hz) x⟩)
      (t - t_ref) (show t - t_ref ∈ Ioo a b from ⟨by
        dsimp only [a]
        linarith, by
        dsimp only [b]
        linarith⟩)
    simpa only [hBmetric, sub_add_cancel] using hresult
  have hterminal : G.limitCarrier.metricComplete (F.metric 0) := by
    obtain ⟨K, hK, hKref⟩ := hbound (-t_ref) (by linarith) ht_ref_mem.2
    simp only [neg_neg] at hKref
    exact metricComplete_terminal_of_closed_slab_curvature_bound
      G.limitCarrier F G.limitFlow.base ht_ref.le hrefSlab hcomplete
      (fun _ _ => ⟨K, hK, fun t ht x _ => hKref t ht x⟩)
  have hbase (k : ℕ) : ((G.embedding k).toFun (0, G.limitFlow.base)).2 =
      (S.flow (G.subsequence k)).base := congrArg Prod.snd (G.base_preserving k)
  have hone : Tendsto
      (fun k => ((Fsrc (G.subsequence k)).connection 0).scalarCurvature
        (((G.embedding k).toFun (0, G.limitFlow.base)).2)) atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually hnormalized] with k hk
    rw [hbase]
    exact hk.symm
  have hnormalizedLimit : (F.connection 0).scalarCurvature G.limitFlow.base = 1 :=
    tendsto_nhds_unique (hreadout 0 hzero G.limitFlow.base).1 hone
  exact {
    carrier := G.limitCarrier
    connectedSpace := connectedSpace_iff_univ.mpr G.limitCarrier.connected
    base := G.limitFlow.base
    flow := F
    zero_mem := hzero
    scalar_normalized := hnormalizedLimit
    complete := by
      intro t ht
      by_cases ht0 : t = 0
      · subst t
        exact hterminal
      · exact hnegativeComplete t ht (lt_of_le_of_ne ht.1 ht0)
    nonnegative_curvature_operator := fun t ht x => (hreadout t ht x).2.2
    curvature_locally_bounded_in_time := by
      intro I hI hIJ
      obtain ⟨l, hl⟩ := (hI.insert t_ref).exists_isLeast (insert_nonempty t_ref I)
      have hl0 : l < 0 := (hl.2 (mem_insert t_ref I)).trans_lt ht_ref
      have hlJ : l ∈ blowupBackwardInterval T0 := by
        rcases hl.1 with rfl | hlI
        · exact ht_ref_mem
        · exact hIJ hlI
      obtain ⟨K, hK, hKl⟩ := hbound (-l) (by linarith) hlJ.2
      simp only [neg_neg] at hKl
      refine ⟨K, hK, fun t ht x => ?_⟩
      rw [abs_of_nonneg (show 0 ≤ (F.connection t).curvatureTensorNorm x from
        Real.sqrt_nonneg _)]
      exact hKl t ⟨hl.2 (mem_insert_of_mem t_ref ht), (hIJ ht).1⟩ x }

end PoincareConjecture.M30
