import PoincareConjecture.Proofs.M14.Mathlib.ContinuousFirstExit

set_option autoImplicit false

open Set

namespace PoincareConjecture

theorem m64_exists_capped_first_exit_open
    {X : Type*} [TopologicalSpace X] {q : ℝ → X} (hq : Continuous q)
    {U : Set X} (hU : IsOpen U) {R eta : ℝ} (hR : 0 < R) (heta : 0 < eta)
    (henter : ∀ t ∈ Ioo (0 : ℝ) eta, q t ∈ U) :
    ∃ b : ℝ, 0 < b ∧ b ≤ R ∧
      (∀ t ∈ Ioo (0 : ℝ) b, q t ∈ U) ∧
      q b ∈ closure U ∧ (b = R ∨ q b ∈ frontier U) := by
  let d := min (eta / 2) (R / 2)
  have hd : 0 < d := lt_min (half_pos heta) (half_pos hR)
  have hdEta : d < eta := (min_le_left _ _).trans_lt (half_lt_self heta)
  have hdR : d < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  have hdU : q d ∈ U := henter d ⟨hd, hdEta⟩
  by_cases hleave : ∃ s ∈ Icc d R, q s ∉ U
  · obtain ⟨b, hb, hbout, hbefore, hclosed⟩ :=
      M14.exists_first_exit_of_continuousOn hq.continuousOn hU hdU hleave
    have hprefix (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) b) : q t ∈ U := by
      by_cases htd : t < d
      · exact henter t ⟨ht.1, htd.trans hdEta⟩
      · exact hbefore ⟨le_of_not_gt htd, ht.2⟩
    have hbclosed : q b ∈ closure U := hclosed ⟨hb.1.le, le_rfl⟩
    refine ⟨b, hd.trans hb.1, hb.2, hprefix, hbclosed, ?_⟩
    by_cases hbR : b = R
    · exact Or.inl hbR
    · right
      rw [frontier, hU.interior_eq]
      exact ⟨hbclosed, hbout⟩
  · refine ⟨R, hR, le_rfl, ?_, ?_, Or.inl rfl⟩
    · intro t ht
      by_cases htd : t < d
      · exact henter t ⟨ht.1, htd.trans hdEta⟩
      · by_contra htU
        exact hleave ⟨t, ⟨le_of_not_gt htd, ht.2.le⟩, htU⟩
    · apply subset_closure
      by_contra hRU
      exact hleave ⟨R, ⟨hdR.le, le_rfl⟩, hRU⟩

theorem m64_capped_first_exit_open_unique
    {X : Type*} [TopologicalSpace X] {q : ℝ → X} {U : Set X} (hU : IsOpen U)
    {R b d : ℝ} (hb : 0 < b) (hd : 0 < d) (hbR : b ≤ R) (hdR : d ≤ R)
    (hbeforeb : ∀ t ∈ Ioo (0 : ℝ) b, q t ∈ U)
    (hbefored : ∀ t ∈ Ioo (0 : ℝ) d, q t ∈ U)
    (hcontactb : b = R ∨ q b ∈ frontier U)
    (hcontactd : d = R ∨ q d ∈ frontier U) : b = d := by
  rcases lt_trichotomy b d with hlt | heq | hlt
  · have hinside := hbefored b ⟨hb, hlt⟩
    rcases hcontactb with hcap | hfront
    · exact False.elim ((not_lt_of_ge (hcap ▸ hdR)) hlt)
    · rw [frontier, hU.interior_eq] at hfront
      exact False.elim (hfront.2 hinside)
  · exact heq
  · have hinside := hbeforeb d ⟨hd, hlt⟩
    rcases hcontactd with hcap | hfront
    · exact False.elim ((not_lt_of_ge (hcap ▸ hbR)) hlt)
    · rw [frontier, hU.interior_eq] at hfront
      exact False.elim (hfront.2 hinside)

theorem m64_capped_first_exit_open_mono
    {X : Type*} [TopologicalSpace X] {q : ℝ → X} {U V : Set X}
    (hUV : U ⊆ V) (hV : IsOpen V) {R b d : ℝ} (hd : 0 < d)
    (hbR : b ≤ R) (hbeforeU : ∀ t ∈ Ioo (0 : ℝ) b, q t ∈ U)
    (hcontactV : d = R ∨ q d ∈ frontier V) : b ≤ d := by
  by_contra hbd
  have hdb : d < b := lt_of_not_ge hbd
  have hdV : q d ∈ V := hUV (hbeforeU d ⟨hd, hdb⟩)
  rcases hcontactV with hcap | hfront
  · exact (not_lt_of_ge hbR) (hcap ▸ hdb)
  · rw [frontier, hV.interior_eq] at hfront
    exact hfront.2 hdV

end PoincareConjecture
