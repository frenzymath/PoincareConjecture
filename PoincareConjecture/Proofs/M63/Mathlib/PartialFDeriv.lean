import Mathlib.Analysis.Calculus.ContDiff.Comp











set_option autoImplicit false

open Set
open scoped ContDiff




theorem ContDiffOn.fderiv_snd_of_isOpen_m63
    {𝕜 E V W : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {m n : ℕ∞ω} {f : E × V → W} {S : Set E} {U : Set V}
    (hf : ContDiffOn 𝕜 n f (S ×ˢ U)) (hU : IsOpen U) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (fun p => fderiv 𝕜 (fun y => f (p.1, y)) p.2) (S ×ˢ U) := by
  have hF : ContDiffOn 𝕜 n (fun p : (E × V) × V => f (p.1.1, p.2))
      ((S ×ˢ U) ×ˢ U) :=
    hf.comp (contDiffOn_fst.fst.prodMk contDiffOn_snd)
      (fun _ hp => ⟨hp.1.1, hp.2⟩)
  intro p hp
  have hD := (hF (p, p.2) ⟨hp, hp.2⟩).fderivWithin
    (f := fun q y => f (q.1, y)) contDiffWithinAt_snd hU.uniqueDiffOn hmn hp
    (fun _ hq => hq.2)
  exact hD.congr_of_mem
    (fun _ hq => (fderivWithin_of_isOpen hU hq.2).symm) hp
