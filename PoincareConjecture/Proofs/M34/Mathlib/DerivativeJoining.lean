import Mathlib.Analysis.Calculus.FDeriv.Extend

set_option autoImplicit false

open Set Filter
open scoped Topology

theorem hasFDerivWithinAt_Icc_prod_of_continuousOn
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ × E → V} {D : ℝ × E → ℝ × E →L[ℝ] V} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b ×ˢ univ))
    (hD : ContinuousOn D (Icc a b ×ˢ univ))
    (hd : ∀ p ∈ Ioo a b ×ˢ univ, HasFDerivAt f (D p) p)
    {p : ℝ × E} (hp : p ∈ Icc a b ×ˢ univ) :
    HasFDerivWithinAt f (D p) (Icc a b ×ˢ univ) p := by
  have hsub : Ioo a b ×ˢ (univ : Set E) ⊆ Icc a b ×ˢ univ :=
    fun _ h => ⟨Ioo_subset_Icc_self h.1, h.2⟩
  have hclosure : closure (Ioo a b ×ˢ (univ : Set E)) = Icc a b ×ˢ univ := by
    simp only [closure_prod_eq, closure_Ioo hab.ne, closure_univ]
  have hlim : Tendsto (fderiv ℝ f) (𝓝[Ioo a b ×ˢ univ] p) (𝓝 (D p)) := by
    apply ((hD p hp).mono hsub).congr'
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (hd q hq).fderiv.symm
  rw [← hclosure]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun q hq => (hd q hq).differentiableAt.differentiableWithinAt)
    ((convex_Ioo a b).prod convex_univ) (isOpen_Ioo.prod isOpen_univ) _ hlim
  intro q hq
  rw [hclosure] at hq
  exact (hf q hq).mono hsub

theorem hasFDerivAt_prod_of_continuousOn_off_time
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ × E → V} {D : ℝ × E → ℝ × E →L[ℝ] V} {a b c : ℝ}
    (hf : ContinuousOn f (Ioo a b ×ˢ univ))
    (hD : ContinuousOn D (Ioo a b ×ˢ univ))
    (hd : ∀ p ∈ Ioo a b ×ˢ univ, p.1 ≠ c → HasFDerivAt f (D p) p)
    {p : ℝ × E} (hp : p ∈ Ioo a b ×ˢ univ) : HasFDerivAt f (D p) p := by
  by_cases hc : p.1 = c
  · have hac : a < c := by simpa only [hc] using hp.1.1
    have hcb : c < b := by simpa only [hc] using hp.1.2
    let l := (a + c) / 2
    let r := (c + b) / 2
    have hl : a < l ∧ l < c := by dsimp [l]; constructor <;> linarith
    have hr : c < r ∧ r < b := by dsimp [r]; constructor <;> linarith
    have hleft : Icc l c ×ˢ (univ : Set E) ⊆ Ioo a b ×ˢ univ := by
      intro q hq
      exact ⟨⟨hl.1.trans_le hq.1.1, hq.1.2.trans_lt hcb⟩, hq.2⟩
    have hright : Icc c r ×ˢ (univ : Set E) ⊆ Ioo a b ×ˢ univ := by
      intro q hq
      exact ⟨⟨hac.trans_le hq.1.1, hq.1.2.trans_lt hr.2⟩, hq.2⟩
    have hdl : HasFDerivWithinAt f (D p) (Icc l c ×ˢ univ) p := by
      apply hasFDerivWithinAt_Icc_prod_of_continuousOn hl.2
        (hf.mono hleft) (hD.mono hleft) _
        ⟨by simpa only [hc] using (show c ∈ Icc l c from ⟨hl.2.le, le_rfl⟩), hp.2⟩
      intro q hq
      exact hd q (hleft ⟨Ioo_subset_Icc_self hq.1, hq.2⟩) hq.1.2.ne
    have hdr : HasFDerivWithinAt f (D p) (Icc c r ×ˢ univ) p := by
      apply hasFDerivWithinAt_Icc_prod_of_continuousOn hr.1
        (hf.mono hright) (hD.mono hright) _
        ⟨by simpa only [hc] using (show c ∈ Icc c r from ⟨le_rfl, hr.1.le⟩), hp.2⟩
      intro q hq
      exact hd q (hright ⟨Ioo_subset_Icc_self hq.1, hq.2⟩) hq.1.1.ne'
    apply (hdl.union hdr).hasFDerivAt
    have hnear : Ioo l r ×ˢ (univ : Set E) ∈ 𝓝 p :=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds
        ⟨by simpa only [hc] using (show c ∈ Ioo l r from ⟨hl.2, hr.1⟩), hp.2⟩
    filter_upwards [hnear] with q hq
    by_cases hqc : q.1 ≤ c
    · exact Or.inl ⟨⟨hq.1.1.le, hqc⟩, hq.2⟩
    · exact Or.inr ⟨⟨(not_le.mp hqc).le, hq.1.2.le⟩, hq.2⟩
  · exact hd p hp hc
