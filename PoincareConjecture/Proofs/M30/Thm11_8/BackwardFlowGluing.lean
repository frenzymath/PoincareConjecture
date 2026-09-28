import PoincareConjecture.Proofs.M30.Thm11_8.BackwardInterval










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30




theorem exists_backwardFlow_of_interior_and_closed
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {T0 : ℝ≥0∞} {τ : ℝ} (hτ : 0 < τ)
    (hhorizon : ENNReal.ofReal τ < T0)
    (Finterior : RicciFlow n M
      {t : ℝ | t < 0 ∧ ENNReal.ofReal (-t) < T0})
    (Fclosed : RicciFlow n M (Icc (-τ) 0))
    (hcompat : ∀ t ∈ Ico (-τ) 0,
      Finterior.metric t = Fclosed.metric t) :
    ∃ F : RicciFlow n M (blowupBackwardInterval T0),
      EqOn F.metric Finterior.metric
        {t : ℝ | t < 0 ∧ ENNReal.ofReal (-t) < T0} ∧
      EqOn F.metric Fclosed.metric (Icc (-τ) 0) := by
  classical
  let W : Set ℝ := {t : ℝ | t < 0 ∧ ENNReal.ofReal (-t) < T0}
  let J := blowupBackwardInterval T0
  let C := Icc (-τ) 0
  have hCJ : C ⊆ J := closedSlab_subset_blowupBackwardInterval hhorizon
  have hJord : J.OrdConnected := by
    refine ⟨?_⟩
    intro x hx y hy z hz
    exact ⟨hz.2.trans hy.1,
      (ENNReal.ofReal_le_ofReal (neg_le_neg hz.1)).trans_lt hx.2⟩
  let slice (t : ℝ) : Sigma (fun g : RiemannianMetric n M => LeviCivitaData g) :=
    if t < 0 then ⟨Finterior.metric t, Finterior.connection t⟩
    else ⟨Fclosed.metric t, Fclosed.connection t⟩
  let g (t : ℝ) := (slice t).1
  have hnegative (t : ℝ) (ht : t < 0) : g t = Finterior.metric t := by
    simp only [g, slice, if_pos ht]
  have hclosed : EqOn g Fclosed.metric C := by
    intro t ht
    by_cases ht0 : t < 0
    · exact (hnegative t ht0).trans (hcompat t ⟨ht.1, ht0⟩)
    · simp only [g, slice, if_neg ht0]
  have hWJ (t : ℝ) (ht : t < 0) : W =ᶠ[𝓝 t] J := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    apply propext
    exact ⟨fun h => ⟨h.1.le, h.2⟩, fun h => ⟨hs, h.2⟩⟩
  have hCJ0 : C =ᶠ[𝓝 (0 : ℝ)] J := by
    filter_upwards [Ioi_mem_nhds (neg_lt_zero.mpr hτ)] with s hs
    apply propext
    exact ⟨fun h => hCJ h, fun h => ⟨hs.le, h.1⟩⟩
  have hg : RiemannianMetric.IsSmoothFamilyOn g J := by
    intro p hp
    by_cases ht : p.1 < 0
    · have hdom : W ×ˢ (univ : Set M) =ᶠ[𝓝 p] J ×ˢ univ := by
        filter_upwards [(hWJ p.1 ht).comp_tendsto (continuous_fst.tendsto p)] with q hq
        exact congrArg (fun a : Prop => a ∧ q.2 ∈ (univ : Set M)) hq
      have hs := (Finterior.smooth p ⟨⟨ht, hp.1.2⟩, hp.2⟩).congr_set hdom
      apply hs.congr_of_eventuallyEq_of_mem ?_ hp
      filter_upwards [((continuous_fst.tendsto p).eventually
        (Iio_mem_nhds ht)).filter_mono nhdsWithin_le_nhds] with q hq
      rw [hnegative q.1 hq]
    · have ht0 : p.1 = 0 := le_antisymm hp.1.1 (le_of_not_gt ht)
      have hpc : p.1 ∈ C := by
        change -τ ≤ p.1 ∧ p.1 ≤ 0
        rw [ht0]
        exact ⟨neg_nonpos.mpr hτ.le, le_rfl⟩
      have htime : C =ᶠ[𝓝 p.1] J := by
        rw [ht0]
        exact hCJ0
      have hdom : C ×ˢ (univ : Set M) =ᶠ[𝓝 p] J ×ˢ univ := by
        filter_upwards [htime.comp_tendsto (continuous_fst.tendsto p)] with q hq
        exact congrArg (fun a : Prop => a ∧ q.2 ∈ (univ : Set M)) hq
      have hs := (Fclosed.smooth p ⟨hpc, hp.2⟩).congr_set hdom
      apply hs.congr_of_eventuallyEq_of_mem ?_ hp
      filter_upwards [(htime.comp_tendsto (continuous_fst.tendsto p)).filter_mono
        nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hq hqJ
      rw [hclosed (Eq.mpr hq hqJ.1)]
  refine ⟨{
    metric := g
    connection := fun t => (slice t).2
    interval := hJord
    nontrivial := Fclosed.nontrivial.mono hCJ
    smooth := hg
    equation := ?_ }, ?_, hclosed⟩
  · intro t ht x v w
    by_cases ht0 : t < 0
    · have hd := (Finterior.equation t ⟨ht0, ht.2⟩ x v w).congr_set (hWJ t ht0)
      have hmetric : (fun s => (g s).inner x v w) =ᶠ[𝓝[J] t]
          (fun s => (Finterior.metric s).inner x v w) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht0)] with s hs
        rw [hnegative s hs]
      have hderiv := hd.congr_of_eventuallyEq_of_mem hmetric ht
      have hs : slice t = ⟨Finterior.metric t, Finterior.connection t⟩ := by
        simp only [slice, if_pos ht0]
      have hr := congrArg (fun q : Sigma (fun g : RiemannianMetric n M =>
        LeviCivitaData g) => q.2.ricci x v w) hs
      change HasDerivWithinAt (fun s => (g s).inner x v w)
        (-2 * (slice t).2.ricci x v w) J t
      rw [hr]
      exact hderiv
    · have htzero : t = 0 := le_antisymm ht.1 (le_of_not_gt ht0)
      subst t
      have hmem : (0 : ℝ) ∈ C := ⟨neg_nonpos.mpr hτ.le, le_rfl⟩
      have hd := (Fclosed.equation 0 hmem x v w).congr_set hCJ0
      have hmetric : (fun s => (g s).inner x v w) =ᶠ[𝓝[J] (0 : ℝ)]
          (fun s => (Fclosed.metric s).inner x v w) := by
        filter_upwards [hCJ0.filter_mono nhdsWithin_le_nhds,
          self_mem_nhdsWithin] with s hs hsJ
        rw [hclosed (Eq.mpr hs hsJ)]
      have hderiv := hd.congr_of_eventuallyEq_of_mem hmetric ht
      have hs : slice 0 = ⟨Fclosed.metric 0, Fclosed.connection 0⟩ := by
        simp only [slice, if_neg (lt_irrefl (0 : ℝ))]
      have hr := congrArg (fun q : Sigma (fun g : RiemannianMetric n M =>
        LeviCivitaData g) => q.2.ricci x v w) hs
      change HasDerivWithinAt (fun s => (g s).inner x v w)
        (-2 * (slice 0).2.ricci x v w) J 0
      rw [hr]
      exact hderiv
  · intro t ht
    exact hnegative t ht.1

end PoincareConjecture.M30
