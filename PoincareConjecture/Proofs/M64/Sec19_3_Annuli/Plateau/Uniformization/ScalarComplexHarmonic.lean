import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarIsothermalEquation
import PoincareConjecture.Proofs.M60.Mathlib.SecondDerivativeChain
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Analytic.IsolatedZeros














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)





theorem scalar_harmonicAt_complex_coordinates {u : Plane → ℝ} {z : ℂ}
    (hu : InnerProductSpace.HarmonicAt u (Complex.orthonormalBasisOneI.repr z)) :
    InnerProductSpace.HarmonicAt (u ∘ Complex.orthonormalBasisOneI.repr) z := by
  let L := Complex.orthonormalBasisOneI.repr.toContinuousLinearMap
  have hL1 : L 1 = EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
    ext i
    fin_cases i <;> simp [L, Complex.orthonormalBasisOneI_repr_apply,
      EuclideanSpace.basisFun_apply]
  have hLI : L Complex.I = EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    ext i
    fin_cases i <;> simp [L, Complex.orthonormalBasisOneI_repr_apply,
      EuclideanSpace.basisFun_apply]
  have hLd : fderiv ℝ (L : ℂ → Plane) = fun _ => L := funext fun _ => L.fderiv
  change InnerProductSpace.HarmonicAt (u ∘ L) z
  refine ⟨hu.1.comp z L.contDiff.contDiffAt, ?_⟩
  filter_upwards [L.continuous.continuousAt.eventually hu.eventually] with w hw
  have h := hw.2.eq_of_nhds
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    u (EuclideanSpace.basisFun (Fin 2) ℝ)] at h
  simp only [Fin.sum_univ_two, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply] at h
  have hd (v q : ℂ) : fderiv ℝ (fderiv ℝ (u ∘ L)) w v q =
      fderiv ℝ (fderiv ℝ u) (L w) (L v) (L q) := by
    rw [M60.second_fderiv_comp hw.1 L.contDiff.contDiffAt]
    simp only [hLd, fderiv_const_apply, zero_apply, map_zero, add_zero]
  simpa only [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Pi.zero_apply, hd, hL1, hLI] using h





theorem scalar_complex_partial_eq_zero_iff (u : ℂ → ℝ) (z : ℂ) :
    ((fderiv ℝ u z 1 : ℂ) - Complex.I * (fderiv ℝ u z Complex.I : ℂ) = 0) ↔
      fderiv ℝ u z = 0 := by
  constructor
  · intro h
    have h1 := congrArg Complex.re h
    have hI := congrArg Complex.im h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.zero_re] at h1
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      mul_zero, Complex.I_im, Complex.ofReal_re, one_mul, zero_add,
      Complex.zero_im, zero_sub, neg_eq_zero] at hI
    ext v
    have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
      simpa only [Complex.real_smul, mul_one] using v.re_add_im.symm
    rw [hv, map_add, map_smul, map_smul, h1, hI]
    simp
  · intro h
    simp [h]





theorem scalar_harmonic_differential_alternative {u : ℂ → ℝ} {z : ℂ}
    (hu : InnerProductSpace.HarmonicAt u z) :
    (∀ᶠ w in 𝓝 z, fderiv ℝ u w = 0) ∨
      ∀ᶠ w in 𝓝[≠] z, fderiv ℝ u w ≠ 0 := by
  simpa only [scalar_complex_partial_eq_zero_iff, ne_eq] using
    (HarmonicAt.analyticAt_complex_partial hu).eventually_eq_zero_or_eventually_ne_zero

end PoincareConjecture.M64Uniformization
