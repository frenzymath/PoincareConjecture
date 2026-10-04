import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.Branch.ComplexConnection
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.SphereArea

/-!
# The harmonic PDE gives the actual local matrix equation

The complex parameter is an actual real linear isometry. Its genuine
derivative chain transports the Laplacian and the connection terms.
Source: Eschenburg--Tribuzy, Conformal mappings of surfaces and
Cauchy--Riemann inequalities, preprint pp. 8--11; M65 derivation 32,
finite-coordinate addendum, for MT Lemma 19.2, printed pp. 438--439.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Complex Filter
open scoped Topology ContDiff BigOperators

namespace PoincareMT.M65Branch

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

/-- The literal harmonic coordinate equation is the actual homogeneous
matrix dbar equation, also at zeros of the differential. Source:
Eschenburg--Tribuzy, pp. 8--11; derivation 32, coordinate addendum. -/
theorem dbar_complexGradient_of_harmonic (D : LeviCivitaData g)
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {z : ℂ}
    (hH : ContDiffAt ℝ ∞ H z)
    (heq : (fderiv ℝ (fderiv ℝ H) z 1 1 + fderiv ℝ (fderiv ℝ H) z I I) +
      (M65Gauss.connectionCoefficient D (H z) (fderiv ℝ H z 1) (fderiv ℝ H z 1) +
        M65Gauss.connectionCoefficient D (H z) (fderiv ℝ H z I) (fderiv ℝ H z I)) = 0) :
    dbar (complexGradient H) z = harmonicMatrix D H z (complexGradient H z) := by
  rw [dbar_complexGradient hH, harmonicMatrix_apply_gradient]
  have hh := congrArg coordinateComplexification heq
  simp only [map_add, map_zero] at hh
  simp only [map_add]
  rw [eq_neg_of_add_eq_zero_left hh]
  simp only [smul_neg, neg_smul]

/-- The actual second differential transforms under the literal
linear parameter equivalence. Source: Eschenburg--Tribuzy, pp. 8--11;
derivation 32, real plane/complex coordinate chain. -/
private theorem secondDeriv_comp_equiv
    (G : LoopPlane → EuclideanSpace ℝ (Fin n)) (e : ℂ ≃L[ℝ] LoopPlane)
    (z u v : ℂ) :
    fderiv ℝ (fderiv ℝ (G ∘ e)) z u v =
      fderiv ℝ (fderiv ℝ G) (e z) (e u) (e v) := by
  have h := e.iteratedFDerivWithin_comp_right G uniqueDiffOn_univ
    (Set.mem_univ (e z)) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  have hh := congrArg (fun T => T ![u, v]) h
  simpa only [iteratedFDeriv_two_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, Matrix.cons_val_zero, Matrix.cons_val_one] using hh

/-- The genuine plane harmonic PDE is preserved by the standard
complex parameter isometry. Source: Eschenburg--Tribuzy, pp. 8--11;
derivation 32, finite-coordinate addendum. -/
theorem plane_harmonic_to_complex (D : LeviCivitaData g)
    {G : LoopPlane → EuclideanSpace ℝ (Fin n)} {z : ℂ}
    (hG : ContDiffAt ℝ ∞ G (orthonormalBasisOneI.repr z))
    (heq : (∑ i : Fin 2, fderiv ℝ (fderiv ℝ G) (orthonormalBasisOneI.repr z)
      (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ i)) +
      ∑ i : Fin 2, M65Gauss.connectionCoefficient D (G (orthonormalBasisOneI.repr z))
        (fderiv ℝ G (orthonormalBasisOneI.repr z) (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (fderiv ℝ G (orthonormalBasisOneI.repr z) (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0) :
    let H := G ∘ orthonormalBasisOneI.repr
    dbar (complexGradient H) z = harmonicMatrix D H z (complexGradient H z) := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let H := G ∘ e
  have hH : ContDiffAt ℝ ∞ H z := hG.comp z e.contDiff.contDiffAt
  have he1 : e 1 = EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
    ext i
    fin_cases i <;> simp [e, orthonormalBasisOneI_repr_apply, EuclideanSpace.basisFun_apply]
  have heI : e I = EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    ext i
    fin_cases i <;> simp [e, orthonormalBasisOneI_repr_apply, EuclideanSpace.basisFun_apply]
  have hd := (hG.differentiableAt (by simp)).hasFDerivAt.comp z e.hasFDerivAt
  have hcol (v : ℂ) : fderiv ℝ H z v = fderiv ℝ G (e z) (e v) :=
    congrArg (fun L : ℂ →L[ℝ] EuclideanSpace ℝ (Fin n) => L v) hd.fderiv
  apply dbar_complexGradient_of_harmonic D hH
  change (fderiv ℝ (fderiv ℝ (G ∘ e)) z 1 1 +
    fderiv ℝ (fderiv ℝ (G ∘ e)) z I I) + _ = 0
  rw [secondDeriv_comp_equiv, secondDeriv_comp_equiv, hcol, hcol, he1, heI]
  simpa only [Fin.sum_univ_two, H, e, Function.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] using heq

end PoincareMT.M65Branch
