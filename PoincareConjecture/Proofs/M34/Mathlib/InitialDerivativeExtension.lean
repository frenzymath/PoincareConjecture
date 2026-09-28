import Mathlib.Analysis.Calculus.FDeriv.Extend









set_option autoImplicit false

open Set Filter
open scoped Topology




theorem hasFDerivWithinAt_Ico_prod_of_continuousOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × E → F} {D : ℝ × E → ℝ × E →L[ℝ] F} {T : ℝ}
    (hf : ContinuousOn f (Ico 0 T ×ˢ univ))
    (hD : ContinuousOn D (Ico 0 T ×ˢ univ))
    (hd : ∀ p ∈ Ioo 0 T ×ˢ univ, HasFDerivAt f (D p) p)
    {p : ℝ × E} (hp : p ∈ Ico 0 T ×ˢ univ) :
    HasFDerivWithinAt f (D p) (Ico 0 T ×ˢ univ) p := by
  rcases p with ⟨t, x⟩
  by_cases ht : t = 0
  · subst t
    have hT : 0 < T := hp.1.2
    have hb : 0 < T / 2 := half_pos hT
    have hbT : T / 2 < T := half_lt_self hT
    let U : Set (ℝ × E) := Ioo 0 (T / 2) ×ˢ univ
    have hsub : U ⊆ Ico 0 T ×ˢ univ := by
      rintro ⟨s, y⟩ ⟨hs, hy⟩
      exact ⟨⟨hs.1.le, hs.2.trans hbT⟩, hy⟩
    have hinside : U ⊆ Ioo 0 T ×ˢ univ := by
      rintro ⟨s, y⟩ ⟨hs, hy⟩
      exact ⟨⟨hs.1, hs.2.trans hbT⟩, hy⟩
    have hclosure : closure U = Icc 0 (T / 2) ×ˢ (univ : Set E) := by
      simp only [U, closure_prod_eq, closure_Ioo hb.ne, closure_univ]
    have hclosedsub : closure U ⊆ Ico 0 T ×ˢ univ := by
      rw [hclosure]
      rintro ⟨s, y⟩ ⟨hs, hy⟩
      exact ⟨⟨hs.1, hs.2.trans_lt hbT⟩, hy⟩
    have hlim : Tendsto (fderiv ℝ f) (𝓝[U] (0, x)) (𝓝 (D (0, x))) := by
      apply ((hD (0, x) hp).mono hsub).congr'
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hd q (hinside hq)).fderiv.symm
    have hderiv : HasFDerivWithinAt f (D (0, x)) (closure U) (0, x) :=
      hasFDerivWithinAt_closure_of_tendsto_fderiv
        (fun q hq => (hd q (hinside hq)).differentiableAt.differentiableWithinAt)
        ((convex_Ioo 0 (T / 2)).prod convex_univ) (isOpen_Ioo.prod isOpen_univ)
        (fun q hq => (hf q (hclosedsub hq)).mono hsub) hlim
    apply hderiv.mono_of_mem_nhdsWithin
    rw [hclosure]
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds
        ((isOpen_Iio.preimage continuous_fst).mem_nhds hb)] with q hq hqb
    exact ⟨⟨hq.1.1, hqb.le⟩, mem_univ q.2⟩
  · exact (hd (t, x) ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm ht), hp.1.2⟩,
      hp.2⟩).hasFDerivWithinAt
