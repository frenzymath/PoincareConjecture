import PoincareConjecture.Proofs.M08.ChartConnectionVariation

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M14

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem closedFamily_timeDerivative_contDiffOn {U : Set E} {C : Set ℝ}
    (hU : IsOpen U) (hC : UniqueDiffOn ℝ C) (q : E × ℝ → F)
    (hq : ContDiffOn ℝ ∞ q (U ×ˢ C)) :
    ContDiffOn ℝ ∞ (fun z => derivWithin (fun s => q (z.1, s)) C z.2) (U ×ˢ C) := by
  let f : ℝ × E → F := fun z => q (z.2, z.1)
  have hf : ContDiffOn ℝ ∞ f (C ×ˢ U) :=
    hq.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hz => ⟨hz.2, hz.1⟩)
  have hD := (M08.timeWithinFDeriv_contDiffOn hC hU f hf).comp
    (contDiffOn_snd.prodMk contDiffOn_fst) (fun z (hz : z ∈ U ×ˢ C) => ⟨hz.2, hz.1⟩)
  apply hD.congr
  intro z hz
  exact (M08.hasDerivWithinAt_timeWithin f hf hz.2 hz.1).derivWithin (hC z.2 hz.2)

end PoincareConjecture.M14
