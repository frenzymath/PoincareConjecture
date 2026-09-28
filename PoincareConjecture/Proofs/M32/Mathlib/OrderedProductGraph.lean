import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter Topology

universe u v

namespace PoincareConjecture.M32

theorem bijective_of_isLocalHomeomorph_ordered_fibers
    {S : Type u} {X : Type v} [TopologicalSpace S] [TopologicalSpace X]
    [CompactSpace S] [ConnectedSpace S] [T2Space X] [ConnectedSpace X]
    (p : S → X) (hp : IsLocalHomeomorph p)
    (h : S → ℝ) (hh : Continuous h)
    (hinj : Function.Injective (fun s => (p s, h s))) : Function.Bijective p := by
  classical
  let A : Set S := {s | ∀ t, p t = p s → h s ≤ h t}
  have hAne : A.Nonempty := by
    obtain ⟨s, _, hmin⟩ := isCompact_univ.exists_isMinOn
      (univ_nonempty : (univ : Set S).Nonempty) hh.continuousOn
    exact ⟨s, fun t _ => hmin (mem_univ t)⟩
  have hAclosed : IsClosed A := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro s hs
    change ¬ ∀ t, p t = p s → h s ≤ h t at hs
    push Not at hs
    obtain ⟨t, hpt, hlt⟩ := hs
    obtain ⟨e, ht, he⟩ := hp t
    have htarget : p s ∈ e.target := by
      rw [← hpt, he]
      exact e.map_source ht
    have hinverse : e.symm (p s) = t := by
      rw [← hpt, he]
      exact e.left_inv ht
    have hj : ContinuousAt (fun y => h (e.symm (p y))) s :=
      hh.continuousAt.comp ((e.continuousAt_symm htarget).comp hp.continuous.continuousAt)
    have hlt' := hj.eventually_lt hh.continuousAt (by simpa [hinverse] using hlt)
    have htarget' := hp.continuous.continuousAt.preimage_mem_nhds
      (e.open_target.mem_nhds htarget)
    filter_upwards [htarget', hlt'] with y hy hly
    change ¬ ∀ t, p t = p y → h y ≤ h t
    intro hmin
    apply (not_le_of_gt hly) (hmin (e.symm (p y)) ?_)
    rw [he]
    exact e.right_inv (by simpa only [mem_preimage, he] using hy)
  have hAopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro s hs
    obtain ⟨e, hes, he⟩ := hp s
    let F : Set S := e.sourceᶜ ∩ p ⁻¹' {p s}
    have hFc : IsCompact F :=
      (e.open_source.isClosed_compl.inter
        (isClosed_singleton.preimage hp.continuous)).isCompact
    have hstrict : ∀ t ∈ F, h s < h t := by
      intro t ht
      have hpt : p t = p s := ht.2
      refine lt_of_le_of_ne (hs t hpt) ?_
      intro hheight
      have hts : t = s := hinj (Prod.ext hpt hheight.symm)
      exact ht.1 (hts.symm ▸ hes)
    obtain ⟨m, hsm, hm⟩ := hFc.exists_forall_le' hh.continuousOn hstrict
    let b := (h s + m) / 2
    have hsb : h s < b := by dsimp only [b]; linarith
    have hbm : b < m := by dsimp only [b]; linarith
    let B : Set S := e.sourceᶜ ∩ {t | h t ≤ b}
    have hBc : IsCompact B :=
      (e.open_source.isClosed_compl.inter (isClosed_le hh continuous_const)).isCompact
    have hpBc : IsClosed (p '' B) := (hBc.image hp.continuous).isClosed
    have hsB : p s ∉ p '' B := by
      rintro ⟨t, ht, hpt⟩
      have hmt := hm t ⟨ht.1, hpt⟩
      exact (not_le_of_gt hbm) (hmt.trans ht.2)
    have hsource := e.open_source.mem_nhds hes
    have houtside := hp.continuous.continuousAt.preimage_mem_nhds
      (hpBc.isOpen_compl.mem_nhds hsB)
    have hheight := (isOpen_lt hh continuous_const).mem_nhds hsb
    filter_upwards [hsource, houtside, hheight] with y hy hyB hyh
    intro t hpt
    by_cases ht : t ∈ e.source
    · have hty : t = y := e.injOn ht hy (by simpa only [← he] using hpt)
      exact le_of_eq (congrArg h hty.symm)
    · have hbt : b < h t := by
        by_contra hnot
        exact hyB ⟨t, ⟨ht, le_of_not_gt hnot⟩, hpt⟩
      exact hyh.le.trans hbt.le
  have hAall : A = univ := (show IsClopen A from ⟨hAclosed, hAopen⟩).eq_univ hAne
  have hmin (s : S) : ∀ t, p t = p s → h s ≤ h t := by
    have : s ∈ A := hAall.symm ▸ mem_univ s
    exact this
  have hpinj : Function.Injective p := by
    intro s t hst
    exact hinj (Prod.ext hst (le_antisymm (hmin s t hst.symm) (hmin t s hst)))
  have hrange : range p = univ := by
    apply (show IsClopen (range p) from ⟨(isCompact_range hp.continuous).isClosed,
      by simpa only [image_univ] using hp.isOpenMap univ isOpen_univ⟩).eq_univ
    exact range_nonempty p
  exact ⟨hpinj, range_eq_univ.mp hrange⟩

end PoincareConjecture.M32
