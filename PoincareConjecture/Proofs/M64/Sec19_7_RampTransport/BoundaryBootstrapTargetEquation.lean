import PoincareConjecture.Proofs.M64.Mathlib.C2LaplacianChange
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapForcing
import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapComplexHessian
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchComplexConnection






noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Complex
open scoped Topology ContDiff BigOperators

namespace PoincareConjecture.M64.RampTransport

open M65Branch

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
variable {n : ℕ}
local notation "Target" => EuclideanSpace ℝ (Fin n)



def boundaryTargetQuadratic (Phi : OpenPartialHomeomorph Target Target)
    (Gamma : Target → Target →L[ℝ] Target →L[ℝ] Target) :
    Target → Target →L[ℝ] Target →L[ℝ] Target := fun y =>
  (ContinuousLinearMap.compL ℝ Target Target Target (fderiv ℝ Phi.symm (Phi y))).comp
      ((Gamma (Phi y)).bilinearComp (fderiv ℝ Phi y) (fderiv ℝ Phi y)) -
    (fderiv ℝ (fderiv ℝ Phi.symm) (Phi y)).bilinearComp
      (fderiv ℝ Phi y) (fderiv ℝ Phi y)



theorem boundaryTargetQuadratic_apply (Phi : OpenPartialHomeomorph Target Target)
    (Gamma : Target → Target →L[ℝ] Target →L[ℝ] Target) (y v w : Target) :
    boundaryTargetQuadratic Phi Gamma y v w =
      fderiv ℝ Phi.symm (Phi y)
          (Gamma (Phi y) (fderiv ℝ Phi y v) (fderiv ℝ Phi y w)) -
        fderiv ℝ (fderiv ℝ Phi.symm) (Phi y)
          (fderiv ℝ Phi y v) (fderiv ℝ Phi y w) := rfl



def boundaryTargetQuadraticCoordinate (Phi : OpenPartialHomeomorph Target Target)
    (Gamma : Target → Target →L[ℝ] Target →L[ℝ] Target) (j : Fin n) :
    Target → Target →L[ℝ] Target →L[ℝ] ℝ := fun y =>
  (ContinuousLinearMap.compL ℝ Target Target ℝ (EuclideanSpace.proj j)).comp
    (boundaryTargetQuadratic Phi Gamma y)



theorem boundaryTargetQuadraticCoordinate_apply
    (Phi : OpenPartialHomeomorph Target Target)
    (Gamma : Target → Target →L[ℝ] Target →L[ℝ] Target)
    (j : Fin n) (y v w : Target) :
    boundaryTargetQuadraticCoordinate Phi Gamma j y v w =
      (boundaryTargetQuadratic Phi Gamma y v w) j := rfl




theorem boundaryTargetQuadratic_contDiffOn
    (Phi : OpenPartialHomeomorph Target Target)
    (hPhi : ContDiffOn ℝ ∞ Phi Phi.source)
    (hPsi : ContDiffOn ℝ ∞ Phi.symm Phi.target)
    {Gamma : Target → Target →L[ℝ] Target →L[ℝ] Target}
    (hGamma : ContDiffOn ℝ ∞ Gamma Phi.target) :
    ContDiffOn ℝ ∞ (boundaryTargetQuadratic Phi Gamma) Phi.source := by
  have hDPhi : ContDiffOn ℝ ∞ (fderiv ℝ Phi) Phi.source :=
    hPhi.fderiv_of_isOpen Phi.open_source (by simp)
  have hDPsi : ContDiffOn ℝ ∞ (fderiv ℝ Phi.symm) Phi.target :=
    hPsi.fderiv_of_isOpen Phi.open_target (by simp)
  have hDDPsi : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ Phi.symm)) Phi.target :=
    hDPsi.fderiv_of_isOpen Phi.open_target (by simp)
  have hG := hGamma.comp hPhi (fun y hy => Phi.map_source hy)
  have hD := hDPsi.comp hPhi (fun y hy => Phi.map_source hy)
  have hDD := hDDPsi.comp hPhi (fun y hy => Phi.map_source hy)
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  change ContDiffOn ℝ ∞ (fun y =>
    fderiv ℝ Phi.symm (Phi y)
        (Gamma (Phi y) (fderiv ℝ Phi y v) (fderiv ℝ Phi y w)) -
      fderiv ℝ (fderiv ℝ Phi.symm) (Phi y)
        (fderiv ℝ Phi y v) (fderiv ℝ Phi y w)) Phi.source
  exact (hD.clm_apply ((hG.clm_apply (hDPhi.clm_apply contDiffOn_const)).clm_apply
    (hDPhi.clm_apply contDiffOn_const))).sub
      ((hDD.clm_apply (hDPhi.clm_apply contDiffOn_const)).clm_apply
        (hDPhi.clm_apply contDiffOn_const))




theorem boundaryTargetQuadraticCoordinate_contDiffOn
    (Phi : OpenPartialHomeomorph Target Target)
    (hPhi : ContDiffOn ℝ ∞ Phi Phi.source)
    (hPsi : ContDiffOn ℝ ∞ Phi.symm Phi.target)
    {Gamma : Target → Target →L[ℝ] Target →L[ℝ] Target}
    (hGamma : ContDiffOn ℝ ∞ Gamma Phi.target) (j : Fin n) :
    ContDiffOn ℝ ∞ (boundaryTargetQuadraticCoordinate Phi Gamma j) Phi.source := by
  have hB := boundaryTargetQuadratic_contDiffOn Phi hPhi hPsi hGamma
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  exact (EuclideanSpace.proj j).contDiff.comp_contDiffOn
    ((hB.clm_apply contDiffOn_const).clm_apply contDiffOn_const)




theorem boundaryTargetQuadratic_equation
    (Phi : OpenPartialHomeomorph Target Target)
    (hPhi : ContDiffOn ℝ ∞ Phi Phi.source)
    (hPsi : ContDiffOn ℝ ∞ Phi.symm Phi.target)
    {Gamma : Target → Target →L[ℝ] Target →L[ℝ] Target}
    {H : Plane → Target} {z : Plane} (hH : ContDiffAt ℝ 2 H z)
    (hz : H z ∈ Phi.target)
    (heq : -(∑ i : Fin 2, fderiv ℝ (fderiv ℝ H) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) =
      ∑ i : Fin 2, Gamma (H z) (fderiv ℝ H z (EuclideanSpace.single i 1))
        (fderiv ℝ H z (EuclideanSpace.single i 1))) :
    -(∑ i : Fin 2, fderiv ℝ (fderiv ℝ (Phi.symm ∘ H)) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) =
      ∑ i : Fin 2, boundaryTargetQuadratic Phi Gamma (Phi.symm (H z))
        (fderiv ℝ (Phi.symm ∘ H) z (EuclideanSpace.single i 1))
        (fderiv ℝ (Phi.symm ∘ H) z (EuclideanSpace.single i 1)) := by
  have hPsiAt : ContDiffAt ℝ 2 Phi.symm (H z) :=
    (hPsi.contDiffAt (Phi.open_target.mem_nhds hz)).of_le (by norm_cast)
  have hu : ContDiffAt ℝ 2 (Phi.symm ∘ H) z := hPsiAt.comp z hH
  have hPhiAt : ContDiffAt ℝ 2 Phi (Phi.symm (H z)) :=
    (hPhi.contDiffAt (Phi.open_source.mem_nhds (Phi.map_target hz))).of_le (by norm_cast)
  have hrec : H =ᶠ[𝓝 z] Phi ∘ (Phi.symm ∘ H) := by
    filter_upwards [hH.continuousAt.preimage_mem_nhds (Phi.open_target.mem_nhds hz)]
      with p hp
    exact (Phi.right_inv hp).symm
  have hcolumn (v : Plane) : fderiv ℝ H z v =
      fderiv ℝ Phi (Phi.symm (H z)) (fderiv ℝ (Phi.symm ∘ H) z v) := by
    rw [hrec.fderiv_eq, fderiv_comp z (hPhiAt.differentiableAt (by norm_num))
      (hu.differentiableAt (by norm_num))]
    rfl
  have hsum := congrArg (fderiv ℝ Phi.symm (H z)) heq
  simp only [map_neg, map_sum] at hsum
  have hrhs : (∑ i : Fin 2, boundaryTargetQuadratic Phi Gamma (Phi.symm (H z))
        (fderiv ℝ (Phi.symm ∘ H) z (EuclideanSpace.single i 1))
        (fderiv ℝ (Phi.symm ∘ H) z (EuclideanSpace.single i 1))) =
      (∑ i : Fin 2, fderiv ℝ Phi.symm (H z)
        (Gamma (H z) (fderiv ℝ H z (EuclideanSpace.single i 1))
          (fderiv ℝ H z (EuclideanSpace.single i 1)))) -
      ∑ i : Fin 2, fderiv ℝ (fderiv ℝ Phi.symm) (H z)
        (fderiv ℝ H z (EuclideanSpace.single i 1))
        (fderiv ℝ H z (EuclideanSpace.single i 1)) := by
    simp only [boundaryTargetQuadratic_apply, Phi.right_inv hz, ← hcolumn,
      Finset.sum_sub_distrib]
  rw [m64C2_laplacian_comp hH hPsiAt, hrhs, ← hsum, map_sum]
  abel




theorem boundaryTargetQuadraticCoordinate_equation
    (Phi : OpenPartialHomeomorph Target Target)
    (hPhi : ContDiffOn ℝ ∞ Phi Phi.source)
    (hPsi : ContDiffOn ℝ ∞ Phi.symm Phi.target)
    {Gamma : Target → Target →L[ℝ] Target →L[ℝ] Target}
    {H : Plane → Target} {z : Plane} (hH : ContDiffAt ℝ 2 H z)
    (hz : H z ∈ Phi.target)
    (heq : -(∑ i : Fin 2, fderiv ℝ (fderiv ℝ H) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) =
      ∑ i : Fin 2, Gamma (H z) (fderiv ℝ H z (EuclideanSpace.single i 1))
        (fderiv ℝ H z (EuclideanSpace.single i 1))) (j : Fin n) :
    -(∑ i : Fin 2, (fderiv ℝ (fderiv ℝ (Phi.symm ∘ H)) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) j) =
      quadraticForcing (boundaryTargetQuadraticCoordinate Phi Gamma j) (Phi.symm ∘ H)
        (fun i => boundaryVectorPartial i (Phi.symm ∘ H)) z := by
  have h := congrArg (EuclideanSpace.proj j)
    (boundaryTargetQuadratic_equation Phi hPhi hPsi hH hz heq)
  simpa only [map_neg, map_sum, EuclideanSpace.proj, PiLp.proj_apply,
    quadraticForcing, boundaryVectorPartial, boundaryTargetQuadraticCoordinate_apply,
    Function.comp_apply] using h




theorem harmonic_laplacian_of_dbar_complexGradient
    {g : RiemannianMetric n Target} (D : LeviCivitaData g)
    {H : ℂ → Target} {z : ℂ} (hH : ContDiffAt ℝ ∞ H z)
    (heq : dbar (complexGradient H) z = harmonicMatrix D H z (complexGradient H z)) :
    -(fderiv ℝ (fderiv ℝ H) z 1 1 + fderiv ℝ (fderiv ℝ H) z I I) =
      M65Gauss.connectionCoefficient D (H z) (fderiv ℝ H z 1) (fderiv ℝ H z 1) +
        M65Gauss.connectionCoefficient D (H z) (fderiv ℝ H z I) (fderiv ℝ H z I) := by
  rw [dbar_complexGradient hH, harmonicMatrix_apply_gradient] at heq
  have h := congrArg (fun v : Fin n → ℂ => (2 : ℂ) • v) heq
  simp only [smul_smul, mul_neg, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0),
    one_smul, neg_one_smul] at h
  apply neg_eq_iff_eq_neg.mpr
  ext j
  have hj := congrArg (fun v : Fin n → ℂ => (v j).re) h
  simpa only [coordinateComplexification, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.comp_apply, EuclideanSpace.proj, PiLp.proj_apply,
    Complex.ofRealCLM_apply, Pi.neg_apply, PiLp.neg_apply,
    Complex.neg_re, Complex.ofReal_re] using hj




theorem boundaryComplexCoordinates_harmonic_equation
    {g : RiemannianMetric n Target} (D : LeviCivitaData g)
    {H : ℂ → Target} {p : Plane}
    (hH : ContDiffAt ℝ ∞ H (boundaryComplexCoordinates p))
    (heq : dbar (complexGradient H) (boundaryComplexCoordinates p) =
      harmonicMatrix D H (boundaryComplexCoordinates p)
        (complexGradient H (boundaryComplexCoordinates p))) :
    -(∑ i : Fin 2, fderiv ℝ (fderiv ℝ (H ∘ boundaryComplexCoordinates)) p
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) =
      ∑ i : Fin 2, M65Gauss.connectionCoefficient D (H (boundaryComplexCoordinates p))
        (fderiv ℝ (H ∘ boundaryComplexCoordinates) p (EuclideanSpace.single i 1))
        (fderiv ℝ (H ∘ boundaryComplexCoordinates) p (EuclideanSpace.single i 1)) := by
  have hcolumn (i : Fin 2) :
      fderiv ℝ (H ∘ boundaryComplexCoordinates) p (EuclideanSpace.single i 1) =
        fderiv ℝ H (boundaryComplexCoordinates p) (if i = 0 then I else 1) := by
    rw [fderiv_comp p (hH.differentiableAt (by simp))
      boundaryComplexCoordinates.differentiableAt,
      show fderiv ℝ boundaryComplexCoordinates p =
        boundaryComplexCoordinates.toContinuousLinearEquiv.toContinuousLinearMap from
          boundaryComplexCoordinates.toContinuousLinearEquiv.fderiv]
    exact congrArg (fderiv ℝ H (boundaryComplexCoordinates p)) (boundaryComplexCoordinates_basis i)
  have h := harmonic_laplacian_of_dbar_complexGradient D hH heq
  simpa only [Fin.sum_univ_two, boundaryComplexCoordinates_hessian hH, hcolumn,
    Fin.isValue, ite_true, Fin.reduceEq, ite_false, add_comm] using h




theorem boundaryTargetQuadraticCoordinate_actual_harmonic
    {g : RiemannianMetric n Target} (D : LeviCivitaData g)
    (Phi : OpenPartialHomeomorph Target Target)
    (hPhi : ContDiffOn ℝ ∞ Phi Phi.source)
    (hPsi : ContDiffOn ℝ ∞ Phi.symm Phi.target)
    {H : ℂ → Target} {p : Plane}
    (hH : ContDiffAt ℝ ∞ H (boundaryComplexCoordinates p))
    (hp : H (boundaryComplexCoordinates p) ∈ Phi.target)
    (heq : dbar (complexGradient H) (boundaryComplexCoordinates p) =
      harmonicMatrix D H (boundaryComplexCoordinates p)
        (complexGradient H (boundaryComplexCoordinates p))) (j : Fin n) :
    let u := Phi.symm ∘ (H ∘ boundaryComplexCoordinates);
    -(∑ i : Fin 2, (fderiv ℝ (fderiv ℝ u) p
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) j) =
      quadraticForcing
        (boundaryTargetQuadraticCoordinate Phi (M65Gauss.connectionCoefficient D) j) u
        (fun i => boundaryVectorPartial i u) p := by
  have hplane : ContDiffAt ℝ 2 (H ∘ boundaryComplexCoordinates) p :=
    (hH.comp p boundaryComplexCoordinates.toContinuousLinearEquiv.contDiff.contDiffAt).of_le
      (by norm_cast)
  exact boundaryTargetQuadraticCoordinate_equation Phi hPhi hPsi hplane hp
    (boundaryComplexCoordinates_harmonic_equation D hH heq) j

end PoincareConjecture.M64.RampTransport
