import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.CanonicalEquation
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Smooth
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ} {U : Set (Spacetime n)}

private theorem smooth_spatial (hU : IsOpen U) {f : Spacetime n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (i : Fin n) :
    ContDiffOn ℝ ∞ (spatialDeriv i f) U :=
  (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

private theorem spatial_mul {f g : Spacetime n → ℝ} {z : Spacetime n}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : Fin n) :
    spatialDeriv i (fun y => f y * g y) z =
      spatialDeriv i f z * g z + f z * spatialDeriv i g z := by
  simp only [spatialDeriv, fderiv_fun_mul hf hg, add_apply,
    smul_apply, smul_eq_mul]
  ring

private theorem spatial_add {f g : Spacetime n → ℝ} {z : Spacetime n}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) (i : Fin n) :
    spatialDeriv i (fun y => f y + g y) z =
      spatialDeriv i f z + spatialDeriv i g z := by
  simp only [spatialDeriv, fderiv_fun_add hf hg, add_apply]

private theorem spatial_mul_second (hU : IsOpen U) {f g : Spacetime n → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    {z : Spacetime n} (hz : z ∈ U) (i j : Fin n) :
    spatialDeriv j (spatialDeriv i (fun y => f y * g y)) z =
      spatialDeriv j (spatialDeriv i f) z * g z +
      spatialDeriv i f z * spatialDeriv j g z +
      spatialDeriv j f z * spatialDeriv i g z +
      f z * spatialDeriv j (spatialDeriv i g) z := by
  have hdiff {v : Spacetime n → ℝ} (hv : ContDiffOn ℝ ∞ v U) :
      DifferentiableAt ℝ v z := (hv.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have heq : spatialDeriv i (fun y => f y * g y) =ᶠ[𝓝 z]
      (fun y => spatialDeriv i f y * g y + f y * spatialDeriv i g y) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact spatial_mul ((hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      ((hg.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)) i
  unfold spatialDeriv at heq ⊢
  rw [heq.fderiv_eq]
  change spatialDeriv j (fun y => spatialDeriv i f y * g y +
    f y * spatialDeriv i g y) z = _
  rw [spatial_add (f := fun y => spatialDeriv i f y * g y)
    (g := fun y => f y * spatialDeriv i g y)
    ((hdiff (smooth_spatial hU hf i)).fun_mul (hdiff hg))
    ((hdiff hf).fun_mul (hdiff (smooth_spatial hU hg i))) j,
    spatial_mul (hdiff (smooth_spatial hU hf i)) (hdiff hg),
    spatial_mul (hdiff hf) (hdiff (smooth_spatial hU hg i))]
  simp only [spatialDeriv]
  change (fderiv ℝ (fun y => fderiv ℝ f y (spatialDirection i)) z (spatialDirection j)) * g z +
      fderiv ℝ f z (spatialDirection i) * fderiv ℝ g z (spatialDirection j) +
      (fderiv ℝ f z (spatialDirection j) * fderiv ℝ g z (spatialDirection i) +
      f z * fderiv ℝ (fun y => fderiv ℝ g y (spatialDirection i)) z (spatialDirection j)) = _
  ring

def forwardCoefficients (a : Fin n → Fin n → Spacetime n → ℝ)
    (b : Fin n → Spacetime n → ℝ) : Coefficients n where
  principal := a
  drift i z := b i z - ∑ j, (spatialDeriv j (a i j) z + spatialDeriv j (a j i) z)
  zeroth z :=
    (∑ i, spatialDeriv i (fun y => b i y -
      ∑ j, (spatialDeriv j (a i j) y + spatialDeriv j (a j i) y)) z) +
    ∑ i, ∑ j, spatialDeriv j (spatialDeriv i (a i j)) z

theorem forwardCoefficients_smooth (hU : IsOpen U)
    {a : Fin n → Fin n → Spacetime n → ℝ} {b : Fin n → Spacetime n → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a i j) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U) :
    (forwardCoefficients a b).IsSmoothOn U := by
  have hd (i) : ContDiffOn ℝ ∞ ((forwardCoefficients a b).drift i) U := by
    apply (hb i).sub
    apply ContDiffOn.sum
    intro j _
    exact (smooth_spatial hU (ha i j) j).add (smooth_spatial hU (ha j i) j)
  refine ⟨ha, hd, ?_⟩
  apply ContDiffOn.add
  · apply ContDiffOn.sum
    intro i _
    exact smooth_spatial hU (hd i) i
  · apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact smooth_spatial hU (smooth_spatial hU (ha i j) i) j

theorem forwardCoefficients_adjoint (hU : IsOpen U)
    {a : Fin n → Fin n → Spacetime n → ℝ} {b : Fin n → Spacetime n → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a i j) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U)
    {φ : Spacetime n → ℝ} (hφ : ContDiffOn ℝ ∞ φ U)
    {z : Spacetime n} (hz : z ∈ U) :
    (forwardCoefficients a b).adjoint φ z =
      -timeDeriv φ z - (∑ i, ∑ j, a i j z * spatialDeriv j (spatialDeriv i φ) z) -
        ∑ i, b i z * spatialDeriv i φ z := by
  have hd := (forwardCoefficients_smooth hU ha hb).2.1
  have hfirst (i) := spatial_mul
    ((hd i).contDiffAt (hU.mem_nhds hz) |>.differentiableAt (by simp))
    (hφ.contDiffAt (hU.mem_nhds hz) |>.differentiableAt (by simp)) i
  have hcross : (∑ i, ∑ j, spatialDeriv i (a i j) z * spatialDeriv j φ z) =
      ∑ i, ∑ j, spatialDeriv j (a j i) z * spatialDeriv i φ z := by
    rw [Finset.sum_comm]
  simp only [Coefficients.adjoint, hfirst]
  dsimp only [forwardCoefficients]
  simp only [spatial_mul_second hU (ha _ _) hφ hz, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_mul, sub_mul, add_mul]
  rw [hcross]
  ring

theorem Coefficients.adjoint_eq_zero_of_notMem_tsupport (C : Coefficients n)
    (φ : Spacetime n → ℝ) {z : Spacetime n} (hz : z ∉ tsupport φ) :
    C.adjoint φ z = 0 := by
  have hd {f : Spacetime n → ℝ} (hs : tsupport f ⊆ tsupport φ)
      (v : Spacetime n) : fderiv ℝ f z v = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ f x v) (fun h => hz (hs
      (tsupport_fderiv_apply_subset ℝ v h)))
  have ha (i j : Fin n) :
      spatialDeriv j (spatialDeriv i (fun y => C.principal i j y * φ y)) z = 0 := by
    apply hd (v := spatialDirection j)
    exact (tsupport_fderiv_apply_subset ℝ (spatialDirection i)).trans tsupport_mul_subset_right
  have hb (i : Fin n) : spatialDeriv i (fun y => C.drift i y * φ y) z = 0 :=
    hd tsupport_mul_subset_right _
  simp only [Coefficients.adjoint, ha, hb, Finset.sum_const_zero,
    timeDeriv, hd Subset.rfl, image_eq_zero_of_notMem_tsupport hz]
  ring

theorem contDiffOn_of_weak_forward_equation (hU : IsOpen U)
    {a : Fin n → Fin n → Spacetime n → ℝ} {b : Fin n → Spacetime n → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a i j) U)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) U)
    (hpos : ∀ z ∈ U, ∀ ξ : Euclid n, ξ ≠ 0 →
      0 < ∑ i, ∑ j, a i j z * ξ i * ξ j)
    {u : Spacetime n → ℝ} (hu : ContinuousOn u U)
    (hw : ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      (∫ z in U, u z * (-timeDeriv φ z -
        (∑ i, ∑ j, a i j z * spatialDeriv j (spatialDeriv i φ) z) -
        ∑ i, b i z * spatialDeriv i φ z)) = 0) :
    ContDiffOn ℝ ∞ u U := by
  apply contDiffOn_of_continuous_weakSolution_positive hU
    (C := forwardCoefficients a b) (forwardCoefficients_smooth hU ha hb) hpos hu
  refine ⟨hu.locallyIntegrableOn hU.measurableSet, ?_⟩
  intro φ hφ hφc hφU
  calc
    (∫ z, u z * (forwardCoefficients a b).adjoint φ z) =
        ∫ z in U, u z * (forwardCoefficients a b).adjoint φ z := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [Coefficients.adjoint_eq_zero_of_notMem_tsupport _ _
        (fun hs => hz (hφU hs)), mul_zero]
    _ = ∫ z in U, u z * (-timeDeriv φ z -
        (∑ i, ∑ j, a i j z * spatialDeriv j (spatialDeriv i φ) z) -
        ∑ i, b i z * spatialDeriv i φ z) := by
      apply setIntegral_congr_fun hU.measurableSet
      intro z hz
      dsimp only
      rw [forwardCoefficients_adjoint hU ha hb hφ.contDiffOn hz]
    _ = 0 := hw φ hφ hφc hφU

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
