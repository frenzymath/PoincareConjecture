import PoincareConjecture.Statements.M67

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture

theorem m68_event_restart_bound
    {a s : ℝ} {f G : ℝ → ℝ}
    (has : a < s)
    (hbound : ∀ t, t ∈ Ioo a s → f t ≤ G t)
    (hleft : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ t, t ∈ Icc a s → s - δ < t → t < s → f s ≤ f t + ε)
    (hG : ContinuousAt G s) : f s ≤ G s := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨δ, hδ, hδall⟩ := hleft (ε / 2) (by linarith)
  have hupper : G s < G s + ε / 2 := by linarith
  have hnhds : G ⁻¹' Iio (G s + ε / 2) ∈ 𝓝 s :=
    hG.preimage_mem_nhds (Iio_mem_nhds hupper)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let d : ℝ := min (δ / 2) (min ((s - a) / 2) (r / 2))
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  let t : ℝ := s - d
  have hta : a < t := by
    dsimp [t]
    have hdle : d ≤ (s - a) / 2 :=
      (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hts : t < s := by
    dsimp [t]
    linarith
  have hst : s - δ < t := by
    dsimp [t]
    have hdle : d ≤ δ / 2 := min_le_left _ _
    linarith
  have htmem : t ∈ Ioo a s := ⟨hta, hts⟩
  have hfg := hbound t htmem
  have hfs := hδall t ⟨le_of_lt hta, hts.le⟩ hst hts
  have habs : dist t s < r := by
    rw [Real.dist_eq]
    dsimp [t]
    have hdle : d ≤ r / 2 :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hdr : d < r := lt_of_le_of_lt hdle (by linarith)
    simpa [abs_of_nonneg hd.le] using hdr
  have hGt : G t < G s + ε / 2 := by
    apply hball
    exact habs
  linarith

end PoincareConjecture
