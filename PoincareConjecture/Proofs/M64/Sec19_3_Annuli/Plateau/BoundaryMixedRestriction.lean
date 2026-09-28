import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryMixedMetricPotential







set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff

namespace PoincareConjecture





theorem m64MixedBoundary_indicator_restrict
    {O W S : Set LoopPlane} (hWO : W ⊆ O) {dirichlet : Prop}
    {F : Fin 2 → LoopPlane → ℝ} {b : LoopPlane → ℝ}
    (heq : ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O → (dirichlet → ∀ p : LoopPlane, p 1 = 0 → phi p = 0) →
      (∫ p, ∑ i : Fin 2, S.indicator (F i) p *
        fderiv ℝ phi p (EuclideanSpace.single i 1)) = ∫ p, S.indicator b p * phi p)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ W)
    (hz : dirichlet → ∀ p : LoopPlane, p 1 = 0 → phi p = 0) :
    (∫ p, ∑ i : Fin 2, (W ∩ S).indicator (F i) p *
      fderiv ℝ phi p (EuclideanSpace.single i 1)) = ∫ p, (W ∩ S).indicator b p * phi p := by
  classical
  have hleft : (fun p => ∑ i : Fin 2, (W ∩ S).indicator (F i) p *
      fderiv ℝ phi p (EuclideanSpace.single i 1)) =
      fun p => ∑ i : Fin 2, S.indicator (F i) p *
        fderiv ℝ phi p (EuclideanSpace.single i 1) := by
    funext p
    by_cases hw : p ∈ W
    · by_cases hS : p ∈ S <;> simp [hw, hS]
    · have hd : fderiv ℝ phi p = 0 :=
        fderiv_of_notMem_tsupport ℝ (fun hh => hw (hs hh))
      simp only [hd, zero_apply, mul_zero, Finset.sum_const_zero]
  have hright : (fun p => (W ∩ S).indicator b p * phi p) =
      fun p => S.indicator b p * phi p := by
    funext p
    by_cases hw : p ∈ W
    · by_cases hS : p ∈ S <;> simp [hw, hS]
    · have hphi : phi p = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hw (hs hh))
      simp only [hphi, mul_zero]
  rw [hleft, hright]
  exact heq phi hp hc (hs.trans hWO) hz

end PoincareConjecture
