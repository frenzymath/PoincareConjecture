import Mathlib.Analysis.Calculus.FDeriv.Extend

namespace Poincare

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivWithinAt_Ici_of_continuousOn
    {a b : ℝ} {f g : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (g t) t) :
    ∀ t ∈ Ico a b, HasDerivWithinAt f (g t) (Ici t) t := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · have hab : a < b := ht.2
    have hgc : ContinuousWithinAt g (Ici a) a := by
      simpa only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hab] using
        hg a ⟨le_rfl, hab.le⟩
    apply hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
      ((hf a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self)
      (Ioo_mem_nhdsGT hab)
    apply (show Tendsto g (𝓝[>] a) (𝓝 (g a)) from
      hgc.mono Ioi_subset_Ici_self).congr'
    filter_upwards [Ioo_mem_nhdsGT hab] with s hs using (hd s hs).deriv.symm
  · exact (hd t ⟨hat, ht.2⟩).hasDerivWithinAt

end Poincare
