import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.PeriodicStripEquation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusMinimumHarmonic






noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M64

open ConnectionVariation





theorem fderiv_eq_of_translation {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (T : E) (hf : ∀ p, f (T + p) = f p) (p : E) :
    fderiv ℝ f (T + p) = fderiv ℝ f p := by
  rw [← fderiv_comp_add_left]
  exact congrArg (fun F => fderiv ℝ F p) (funext hf)





def annulusWeightedTension {n : ℕ}
    (Gamma : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (u : LoopPlane → EuclideanSpace ℝ (Fin n)) (r : ℝ) (p : LoopPlane) :
    EuclideanSpace ℝ (Fin n) :=
  r • covDerivAlong Gamma u (fun z => fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ 0))
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) p +
    r⁻¹ • covDerivAlong Gamma u (fun z => fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ 1))
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) p





theorem annulusWeightedTension_periodic {n : ℕ}
    (Gamma : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)} (r : ℝ)
    (hu : ∀ x s, u (annulusPoint (x + curvePeriod) s) = u (annulusPoint x s)) :
    ∀ x s, annulusWeightedTension Gamma u r (annulusPoint (x + curvePeriod) s) =
      annulusWeightedTension Gamma u r (annulusPoint x s) := by
  let T := annulusPoint curvePeriod 0
  have huT (p : LoopPlane) : u (T + p) = u p := by
    simpa only [one_smul] using annulus_periodic_integer_translate hu 1 p
  have hdu (p : LoopPlane) := fderiv_eq_of_translation T huT p
  have hv (i : Fin 2) (p : LoopPlane) :
      fderiv ℝ u (T + p) (EuclideanSpace.basisFun (Fin 2) ℝ i) =
        fderiv ℝ u p (EuclideanSpace.basisFun (Fin 2) ℝ i) := by rw [hdu]
  have hdv (i : Fin 2) (p : LoopPlane) := fderiv_eq_of_translation
    (f := fun z => fderiv ℝ u z (EuclideanSpace.basisFun (Fin 2) ℝ i)) T (hv i) p
  have htau (p : LoopPlane) : annulusWeightedTension Gamma u r (T + p) =
      annulusWeightedTension Gamma u r p := by
    simp only [annulusWeightedTension, covDerivAlong_def, huT, hdu, hdv]
  intro x s
  have hshift : annulusPoint (x + curvePeriod) s = T + annulusPoint x s := by
    ext i
    fin_cases i <;> simp [T, annulusPoint, add_comm]
  rw [hshift]
  exact htau _






theorem annulusWeightedTension_contDiffOn {n : ℕ}
    {Gamma : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)} (r : ℝ) {U : Set LoopPlane}
    (hU : IsOpen U) (hu : ContDiffOn ℝ ∞ u U)
    (hGamma : ∀ p ∈ U, ContDiffAt ℝ ∞ Gamma (u p)) :
    ContDiffOn ℝ ∞ (annulusWeightedTension Gamma u r) U := by
  intro p hp
  have hup := hu.contDiffAt (hU.mem_nhds hp)
  have hi (i : Fin 2) : ContDiffAt ℝ ∞
      (fun z => covDerivAlong Gamma u
        (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (EuclideanSpace.basisFun (Fin 2) ℝ i) z) p :=
    contDiffAt_covDerivAlong (hGamma p hp) hup
      ((hup.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const)
      (EuclideanSpace.basisFun (Fin 2) ℝ i)
  exact (((contDiffAt_const (c := r)).smul (hi 0)).add
    ((contDiffAt_const (c := r⁻¹)).smul (hi 1))).contDiffWithinAt

end PoincareConjecture.M64
