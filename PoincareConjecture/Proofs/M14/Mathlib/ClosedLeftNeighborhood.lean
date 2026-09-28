import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M14

theorem exists_closed_left_neighborhood {a b t : ℝ} (hat : a < t) (htb : t ≤ b)
    {S : Set ℝ} (hS : S ∈ 𝓝[Icc a b] t) :
    ∃ c d : ℝ, a < c ∧ c < t ∧ t ≤ d ∧ d ≤ b ∧ Icc c d ⊆ S ∧
      Icc c d ∈ 𝓝[Icc a b] t := by
  obtain ⟨N, hN, htN, hNS⟩ := mem_nhdsWithin.mp hS
  obtain ⟨l, u, ⟨hlt, htu⟩, hln⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hN.mem_nhds htN)
  let c := (max a l + t) / 2
  let e := (t + u) / 2
  let d := min b e
  have hmt : max a l < t := max_lt hat hlt
  have hmc : max a l < c := by dsimp only [c]; linarith
  have hct : c < t := by dsimp only [c]; linarith
  have hac : a < c := (le_max_left _ _).trans_lt hmc
  have hlc : l < c := (le_max_right _ _).trans_lt hmc
  have hte : t < e := by dsimp only [e]; linarith
  have heu : e < u := by dsimp only [e]; linarith
  have htd : t ≤ d := le_min htb hte.le
  refine ⟨c, d, hac, hct, htd, min_le_left _ _, ?_, ?_⟩
  · intro s hs
    exact hNS ⟨hln ⟨hlc.trans_le hs.1, hs.2.trans_lt ((min_le_right _ _).trans_lt heu)⟩,
      hac.le.trans hs.1, hs.2.trans (min_le_left _ _)⟩
  · exact mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Ioo c e, Ioo_mem_nhds hct hte, fun s hs => ⟨hs.1.1.le, le_min hs.2.2 hs.1.2.le⟩⟩

theorem left_lt_of_Icc_mem_nhdsWithin {a b c d t : ℝ} (hat : a < t) (htb : t ≤ b)
    (hnear : Icc c d ∈ 𝓝[Icc a b] t) : c < t := by
  obtain ⟨l, r, _, hlt, htr, _, hsub, _⟩ := exists_closed_left_neighborhood hat htb hnear
  exact (hsub ⟨le_rfl, hlt.le.trans htr⟩).1.trans_lt hlt

end PoincareConjecture.M14
