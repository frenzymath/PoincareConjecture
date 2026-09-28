import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]



theorem ContDiffOn.fderiv_snd_of_isOpen {f : E × F → G} {S : Set E} {U : Set F}
    (hf : ContDiffOn 𝕜 ∞ f (S ×ˢ U)) (hU : IsOpen U) :
    ContDiffOn 𝕜 ∞ (fun z : E × F => fderiv 𝕜 (fun y => f (z.1, y)) z.2)
      (S ×ˢ U) := by
  intro z hz
  have hmap : MapsTo (fun p : (E × F) × F => (p.1.1, p.2))
      ((S ×ˢ U) ×ˢ U) (S ×ˢ U) := fun _ hp => ⟨hp.1.1, hp.2⟩
  have hh : ContDiffWithinAt 𝕜 ∞
      (fun p : (E × F) × F => f (p.1.1, p.2)) ((S ×ˢ U) ×ˢ U) (z, z.2) :=
    (hf z hz).comp (z, z.2)
      (contDiffWithinAt_fst.fst.prodMk contDiffWithinAt_snd) hmap
  have hd : ContDiffWithinAt 𝕜 ∞
      (fun p : E × F => fderivWithin 𝕜 (fun y : F => f (p.1, y)) U p.2)
      (S ×ˢ U) z := hh.fderivWithin (f := fun (p : E × F) (y : F) => f (p.1, y))
    (g := fun p : E × F => p.2) contDiffWithinAt_snd hU.uniqueDiffOn (by simp) hz
    (fun _ hp => hp.2)
  apply hd.congr_of_eventuallyEq_of_mem _ hz
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (fderivWithin_of_isOpen hU hp.2).symm



theorem ContDiffOn.iteratedFDeriv_snd_of_isOpen {f : E × F → G} {S : Set E} {U : Set F}
    (hf : ContDiffOn 𝕜 ∞ f (S ×ˢ U)) (hU : IsOpen U) (m : ℕ) :
    ContDiffOn 𝕜 ∞
      (fun z : E × F => iteratedFDeriv 𝕜 m (fun y => f (z.1, y)) z.2) (S ×ˢ U) := by
  induction m with
  | zero =>
      let e := (continuousMultilinearCurryFin0 𝕜 F G).symm.toContinuousLinearEquiv
      exact e.toContinuousLinearMap.contDiff.comp_contDiffOn hf
  | succ m ih =>
      let e := (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (m + 1) => F) G).symm
      convert! e.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn
        (ih.fderiv_snd_of_isOpen hU) using 1
