import Mathlib.Analysis.Calculus.ContDiff.Comp










set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareConjecture.M47



theorem terminalGerms_contDiffOn_spatial_jets
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : Set ℝ} {U : Set E} (hU : IsOpen U)
    {f : ℝ × E → F} (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) (m : ℕ) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E => iteratedFDeriv ℝ m (fun y => f (p.1, y)) p.2) (J ×ˢ U) := by
  induction m with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp_contDiffOn hf
  | succ m ih =>
    have hpartial : ContDiffOn ℝ ∞
        (fun p : ℝ × E => fderivWithin ℝ
          (fun y => iteratedFDeriv ℝ m (fun z => f (p.1, z)) y) U p.2) (J ×ˢ U) := by
      intro p hp
      have hmap : ContDiff ℝ ∞
          (fun q : (ℝ × E) × E => (q.1.1, q.2)) :=
        (contDiff_fst.fst).prodMk contDiff_snd
      have hc := (ih p hp).comp (p, p.2) hmap.contDiffWithinAt
        (show MapsTo (fun q : (ℝ × E) × E => (q.1.1, q.2))
          ((J ×ˢ U) ×ˢ U) (J ×ˢ U) from fun q hq => ⟨hq.1.1, hq.2⟩)
      exact ContDiffWithinAt.fderivWithin
        (f := fun (q : ℝ × E) y => iteratedFDeriv ℝ m (fun z => f (q.1, z)) y)
        (g := Prod.snd) hc contDiffWithinAt_snd hU.uniqueDiffOn (by simp) hp
        (fun q hq => hq.2)
    have hnext := (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (m + 1) => E) F).symm.contDiff.comp_contDiffOn hpartial
    apply hnext.congr
    intro p hp
    change iteratedFDeriv ℝ (m + 1) (fun z => f (p.1, z)) p.2 =
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F).symm
        (fderivWithin ℝ (iteratedFDeriv ℝ m (fun z => f (p.1, z))) U p.2)
    rw [fderivWithin_of_mem_nhds (hU.mem_nhds hp.2)]
    exact congrFun iteratedFDeriv_succ_eq_comp_left p.2

end PoincareConjecture.M47
