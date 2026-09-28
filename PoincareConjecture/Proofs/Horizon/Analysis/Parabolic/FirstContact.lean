import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.CompactMaximum
import Mathlib.Topology.Order.IntermediateValue












set_option autoImplicit false

open Set

namespace Poincare.Parabolic




theorem pos_of_deriv_pos_at_first_zero_of_pos_outside_compact
    {X : Type*} [TopologicalSpace X]
    {F F' : X → ℝ → ℝ} {a b : ℝ} {K : Set X} (hK : IsCompact K)
    (hF : ContinuousOn (Function.uncurry F) (univ ×ˢ Icc a b))
    (hderiv : ∀ q t, t ∈ Ioc a b →
      HasDerivWithinAt (F q) (F' q t) (Icc a b) t)
    (hcontact : ∀ q t, t ∈ Ioc a b → F q t = 0 →
      (∀ p, 0 ≤ F p t) → 0 < F' q t)
    (hinit : ∀ q, 0 < F q a)
    (houtside : ∀ q ∉ K, ∀ t ∈ Icc a b, 0 < F q t) :
    ∀ q t, t ∈ Icc a b → 0 < F q t := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have htime (q : X) : ContinuousOn (F q) (Icc a b) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨trivial, hs⟩)
  have hroot (q : X) {t : ℝ} (ht : t ∈ Icc a b) (hqt : F q t ≤ 0) :
      ∃ s ∈ Icc a t, F q s = 0 :=
    intermediate_value_Icc' ht.1
      ((htime q).mono (Icc_subset_Icc_right ht.2)) ⟨hqt, (hinit q).le⟩
  have hzero_mem (q : X) {t : ℝ} (ht : t ∈ Icc a b) (hz : F q t = 0) :
      q ∈ K := by
    by_contra hq
    have hp := houtside q hq t ht
    linarith
  let Z : Set (K × Icc a b) := {z | F z.1 z.2 = 0}
  have hcont : Continuous (fun z : K × Icc a b => F z.1 z.2) :=
    hF.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun z => ⟨trivial, z.2.property⟩)
  have hZ : IsCompact Z := (isClosed_eq hcont continuous_const).isCompact
  intro q t ht
  by_contra hpos
  obtain ⟨r, hr, hqr⟩ := hroot q ht (le_of_not_gt hpos)
  have hr' : r ∈ Icc a b := ⟨hr.1, hr.2.trans ht.2⟩
  have hne : Z.Nonempty := ⟨(⟨q, hzero_mem q hr' hqr⟩, ⟨r, hr'⟩), hqr⟩
  obtain ⟨z, hz, hmin⟩ := hZ.exists_isMinOn hne
    (continuous_subtype_val.comp continuous_snd).continuousOn
  have haz : a < (z.2 : ℝ) := lt_of_le_of_ne z.2.property.1 (by
    intro heq
    have hp := hinit z.1
    change F z.1 z.2 = 0 at hz
    rw [← heq] at hz
    linarith)
  have hnonneg (p : X) {s : ℝ} (hs : s ∈ Icc a (z.2 : ℝ)) :
      0 ≤ F p s := by
    by_contra hp
    have hneg : F p s < 0 := lt_of_not_ge hp
    have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans z.2.property.2⟩
    obtain ⟨r, hr, hpr⟩ := hroot p hs' hneg.le
    have hrs : r < s := lt_of_le_of_ne hr.2 (by
      intro heq
      rw [heq] at hpr
      linarith)
    have hr' : r ∈ Icc a b := ⟨hr.1, hr.2.trans hs'.2⟩
    have hm := hmin (a := (⟨p, hzero_mem p hr' hpr⟩, ⟨r, hr'⟩)) hpr
    exact (not_lt_of_ge hm) (hrs.trans_le hs.2)
  have hzt : (z.2 : ℝ) ∈ Ioc a b := ⟨haz, z.2.property.2⟩
  have hder := (hderiv z.1 z.2 hzt).mono
    (Icc_subset_Icc_right z.2.property.2)
  have htime_min : IsMinOn (F z.1) (Icc a (z.2 : ℝ)) z.2 := by
    intro s hs
    change F z.1 z.2 ≤ F z.1 s
    rw [show F z.1 z.2 = 0 from hz]
    exact hnonneg z.1 hs
  have hcone : a - (z.2 : ℝ) ∈ posTangentConeAt (Icc a (z.2 : ℝ)) z.2 :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc a (z.2 : ℝ)).segment_subset ⟨haz.le, le_rfl⟩ ⟨le_rfl, haz.le⟩)
  have hd := htime_min.localize.hasFDerivWithinAt_nonneg hder.hasFDerivWithinAt hcone
  change 0 ≤ (a - (z.2 : ℝ)) * F' z.1 z.2 at hd
  have hp := hcontact z.1 z.2 hzt hz
    (fun p => hnonneg p ⟨haz.le, le_rfl⟩)
  nlinarith

end Poincare.Parabolic
