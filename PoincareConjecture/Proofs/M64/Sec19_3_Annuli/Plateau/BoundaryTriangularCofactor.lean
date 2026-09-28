import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryTriangularDerivative












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)



theorem m64TriangularSource_scalar_comp_zero
    {T : LoopPlane → LoopPlane} (hT : Differentiable ℝ T)
    (hsecond : ∀ p, T p 1 = p 1) {phi : LoopPlane → ℝ}
    (hp : Differentiable ℝ phi) (p : LoopPlane) :
    fderiv ℝ (phi ∘ T) p e0 = fderiv ℝ T p e0 0 * fderiv ℝ phi (T p) e0 := by
  rw [fderiv_comp p (hp _) (hT _), ContinuousLinearMap.comp_apply]
  have hcol : fderiv ℝ T p e0 = (fderiv ℝ T p e0 0) • e0 := by
    ext i
    fin_cases i
    · simp
    · change fderiv ℝ T p e0 1 = _
      rw [m64TriangularSource_second_derivative hT hsecond]
      simp
  conv_lhs => rw [hcol, map_smul]
  rfl



theorem m64TriangularSource_scalar_comp_one
    {T : LoopPlane → LoopPlane} (hT : Differentiable ℝ T)
    (hsecond : ∀ p, T p 1 = p 1) {phi : LoopPlane → ℝ}
    (hp : Differentiable ℝ phi) (p : LoopPlane) :
    fderiv ℝ (phi ∘ T) p e1 =
      fderiv ℝ T p e1 0 * fderiv ℝ phi (T p) e0 + fderiv ℝ phi (T p) e1 := by
  rw [fderiv_comp p (hp _) (hT _), ContinuousLinearMap.comp_apply]
  have hcol : fderiv ℝ T p e1 = (fderiv ℝ T p e1 0) • e0 + e1 := by
    ext i
    fin_cases i
    · simp
    · change fderiv ℝ T p e1 1 = _
      rw [m64TriangularSource_second_derivative hT hsecond]
      simp
  conv_lhs => rw [hcol, map_add, map_smul]
  rfl




theorem m64Source_first_coordinate_derivative
    {T : LoopPlane → LoopPlane} (hT : Differentiable ℝ T) (p v : LoopPlane) :
    fderiv ℝ (fun q => T q 0) p v = fderiv ℝ T p v 0 := by
  let L : LoopPlane →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hd := (L.hasFDerivAt.comp p (hT p).hasFDerivAt).fderiv
  exact congrArg (fun A : LoopPlane →L[ℝ] ℝ => A v) hd



def m64TriangularCofactorTest0 (T : LoopPlane ≃ₜ LoopPlane) (phi : LoopPlane → ℝ)
    (p : LoopPlane) : ℝ :=
  -(fderiv ℝ (fun q => T.symm q 0) p e1) * phi (T.symm p)



def m64TriangularCofactorTest1 (T : LoopPlane ≃ₜ LoopPlane) (phi : LoopPlane → ℝ)
    (p : LoopPlane) : ℝ :=
  (fderiv ℝ (fun q => T.symm q 0) p e0) * phi (T.symm p)



theorem m64TriangularCofactorTest_contDiff
    (T : LoopPlane ≃ₜ LoopPlane) (hi : ContDiff ℝ ∞ T.symm)
    {phi : LoopPlane → ℝ} {q : WithTop ℕ∞} (hp : ContDiff ℝ q phi) (hq : q ≤ ∞) :
    ContDiff ℝ q (m64TriangularCofactorTest0 T phi) ∧
      ContDiff ℝ q (m64TriangularCofactorTest1 T phi) := by
  have hu : ContDiff ℝ ∞ (fun p => T.symm p 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).contDiff.comp hi
  have hdu : ContDiff ℝ ∞ (fderiv ℝ (fun p => T.symm p 0)) :=
    hu.fderiv_right (by simp)
  have hpsi : ContDiff ℝ q (phi ∘ T.symm) := hp.comp (hi.of_le hq)
  exact ⟨(((hdu.of_le hq).clm_apply contDiff_const).neg).mul hpsi,
    ((hdu.of_le hq).clm_apply contDiff_const).mul hpsi⟩




theorem m64TriangularCofactor_divergence
    (T : LoopPlane ≃ₜ LoopPlane) (hi : ContDiff ℝ ∞ T.symm)
    (hsecond : ∀ p, T p 1 = p 1) {phi : LoopPlane → ℝ} (hp : ContDiff ℝ 1 phi)
    (p : LoopPlane) :
    fderiv ℝ (m64TriangularCofactorTest0 T phi) p e0 +
      fderiv ℝ (m64TriangularCofactorTest1 T phi) p e1 =
      fderiv ℝ (fun q => T.symm q 0) p e0 * fderiv ℝ phi (T.symm p) e1 := by
  let u := fun p : LoopPlane => T.symm p 0
  let d := fun (i : Fin 2) (p : LoopPlane) => fderiv ℝ u p (EuclideanSpace.single i 1)
  let psi := phi ∘ T.symm
  have hu : ContDiff ℝ ∞ u :=
    (EuclideanSpace.proj (0 : Fin 2) : LoopPlane →L[ℝ] ℝ).contDiff.comp hi
  have hd (i : Fin 2) : ContDiff ℝ 1 (d i) :=
    ((hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) p :=
    ((hu.contDiffAt).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hswap : fderiv ℝ (d 1) p e0 = fderiv ℝ (d 0) p e1 := by
    have hsymm := (hu.contDiffAt (x := p)).isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top) e0 e1
    dsimp only [d]
    rw [fderiv_clm_apply hfd (differentiableAt_const e1),
      fderiv_clm_apply hfd (differentiableAt_const e0)]
    simpa using hsymm
  have hip := hi.differentiable (by simp)
  have hpsi : Differentiable ℝ psi := (hp.differentiable (by simp)).comp hip
  have hd0 : fderiv ℝ psi p e0 = d 0 p * fderiv ℝ phi (T.symm p) e0 := by
    rw [m64TriangularSource_scalar_comp_zero hip (m64TriangularSource_inverse_second T hsecond)
      (hp.differentiable (by simp))]
    rw [show d 0 p = fderiv ℝ T.symm p e0 0 from m64Source_first_coordinate_derivative hip p e0]
  have hd1 : fderiv ℝ psi p e1 =
      d 1 p * fderiv ℝ phi (T.symm p) e0 + fderiv ℝ phi (T.symm p) e1 := by
    rw [m64TriangularSource_scalar_comp_one hip (m64TriangularSource_inverse_second T hsecond)
      (hp.differentiable (by simp))]
    rw [show d 1 p = fderiv ℝ T.symm p e1 0 from m64Source_first_coordinate_derivative hip p e1]
  change fderiv ℝ ((-d 1) * psi) p e0 + fderiv ℝ ((d 0) * psi) p e1 =
    d 0 p * fderiv ℝ phi (T.symm p) e1
  rw [fderiv_mul ((hd 1).differentiable (by simp) p).neg (hpsi p),
    fderiv_mul ((hd 0).differentiable (by simp) p) (hpsi p),
    fderiv_neg]
  simp only [add_apply, smul_apply, neg_apply, Pi.neg_apply, smul_eq_mul, hswap, hd0, hd1]
  ring

end PoincareConjecture
