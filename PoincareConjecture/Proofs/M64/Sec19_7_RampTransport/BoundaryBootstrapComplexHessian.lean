import PoincareConjecture.Proofs.M64.Sec19_7_RampTransport.BoundaryBootstrapClassicalJets
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryCoordinateSwap
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchComplexGradient
import PoincareConjecture.Proofs.M60.Mathlib.SecondDerivativeChain
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Complex
open scoped ContDiff ENNReal Topology

namespace PoincareConjecture.M64.RampTransport

open M65Branch Poincare.Analysis.Sobolev.Euclidean

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {n : ℕ}
local notation "Target" => EuclideanSpace ℝ (Fin n)

theorem complexGradient_fderiv_apply {H : ℂ → Target} {z : ℂ}
    (hH : ContDiffAt ℝ ∞ H z) (v : ℂ) :
    fderiv ℝ (complexGradient H) z v =
      coordinateComplexification (fderiv ℝ (fderiv ℝ H) z v 1) -
        I • coordinateComplexification (fderiv ℝ (fderiv ℝ H) z v I) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ H) z :=
    (hH.fderiv_right (m := 1)
      (WithTop.coe_le_coe.mpr le_top)).differentiableAt (by simp)
  have hc (w : ℂ) := coordinateComplexification.hasFDerivAt.comp z
    (hd.hasFDerivAt.clm_apply (hasFDerivAt_const w z))
  have hder := (hc 1).sub ((hc I).const_smul I)
  change HasFDerivAt (complexGradient H) _ z at hder
  simp only [hder.fderiv, ContinuousLinearMap.comp_apply, sub_apply, smul_apply,
    add_apply, ContinuousLinearMap.flip_apply, zero_apply, map_zero, zero_add]

theorem complexGradient_hessian_memLp {O : Set ℂ} (hO : IsOpen O)
    {H : ℂ → Target} (hH : ContDiffOn ℝ ∞ H O) {v : ℂ}
    (hG : MemLp (fun z => fderiv ℝ (complexGradient H) z v) 2 (volume.restrict O)) :
    MemLp (fun z => fderiv ℝ (fderiv ℝ H) z v 1) 2 (volume.restrict O) ∧
      MemLp (fun z => fderiv ℝ (fderiv ℝ H) z v I) 2 (volume.restrict O) := by
  have heq (z : ℂ) (hz : z ∈ O) (j : Fin n) :
      (fderiv ℝ (complexGradient H) z v) j =
        ((fderiv ℝ (fderiv ℝ H) z v 1) j : ℂ) -
          I * ((fderiv ℝ (fderiv ℝ H) z v I) j : ℂ) := by
    rw [complexGradient_fderiv_apply (hH.contDiffAt (hO.mem_nhds hz))]
    rfl
  constructor
  · apply MemLp.of_eval_piLp
    intro j
    apply MemLp.ae_eq ?_ (Complex.reCLM.comp_memLp' (hG.eval j))
    filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
    change ((fderiv ℝ (complexGradient H) z v) j).re = _
    rw [heq z hz j]
    simp
  · apply MemLp.of_eval_piLp
    intro j
    apply MemLp.ae_eq ?_ (Complex.imCLM.comp_memLp' (hG.eval j)).neg
    filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
    change -((fderiv ℝ (complexGradient H) z v) j).im = _
    rw [heq z hz j]
    simp

def boundaryComplexCoordinates : Plane ≃ₗᵢ[ℝ] ℂ :=
  m64BoundaryCoordinateSwap.trans Complex.orthonormalBasisOneI.repr.symm

theorem boundaryComplexCoordinates_basis (i : Fin 2) :
    boundaryComplexCoordinates (EuclideanSpace.single i 1) = if i = 0 then I else 1 := by
  simp only [boundaryComplexCoordinates, LinearIsometryEquiv.trans_apply,
    m64BoundaryCoordinateSwap_basis, Complex.orthonormalBasisOneI_repr_symm_apply]
  fin_cases i <;> simp

theorem boundaryComplexCoordinates_hessian {H : ℂ → Target} {p : Plane}
    (hH : ContDiffAt ℝ ∞ H (boundaryComplexCoordinates p)) (a b : Fin 2) :
    fderiv ℝ (fderiv ℝ (H ∘ boundaryComplexCoordinates)) p
        (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) =
      fderiv ℝ (fderiv ℝ H) (boundaryComplexCoordinates p)
        (if a = 0 then I else 1) (if b = 0 then I else 1) := by
  let e := boundaryComplexCoordinates.toContinuousLinearEquiv.toContinuousLinearMap
  have hs : ContDiffAt ℝ 2 boundaryComplexCoordinates p := e.contDiff.contDiffAt
  rw [M60.second_fderiv_comp (hH.of_le (WithTop.coe_le_coe.mpr le_top)) hs]
  change fderiv ℝ (fderiv ℝ H) (boundaryComplexCoordinates p)
      (fderiv ℝ e p (EuclideanSpace.single a 1))
      (fderiv ℝ e p (EuclideanSpace.single b 1)) +
      fderiv ℝ H (boundaryComplexCoordinates p)
        (fderiv ℝ (fderiv ℝ e) p (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) = _
  rw [show fderiv ℝ e = fun _ : Plane => e from funext fun _ => e.fderiv]
  simp only [fderiv_const_apply, zero_apply, map_zero, add_zero]
  exact congrArg₂ (fun v w => fderiv ℝ (fderiv ℝ H) (boundaryComplexCoordinates p) v w)
    (boundaryComplexCoordinates_basis a) (boundaryComplexCoordinates_basis b)

theorem boundaryComplexCoordinates_hessian_memLp {O : Set ℂ} (hO : IsOpen O)
    {H : ℂ → Target} (hH : ContDiffOn ℝ ∞ H O)
    (h1 : MemLp (fun z => fderiv ℝ (complexGradient H) z 1) 2 (volume.restrict O))
    (hI : MemLp (fun z => fderiv ℝ (complexGradient H) z I) 2 (volume.restrict O))
    (a b : Fin 2) :
    MemLp (fun p => fderiv ℝ (fderiv ℝ (H ∘ boundaryComplexCoordinates)) p
      (EuclideanSpace.single a 1) (EuclideanSpace.single b 1))
      2 (volume.restrict (boundaryComplexCoordinates ⁻¹' O)) := by
  have hpair1 := complexGradient_hessian_memLp hO hH h1
  have hpairI := complexGradient_hessian_memLp hO hH hI
  have hraw : MemLp (fun z => fderiv ℝ (fderiv ℝ H) z
      (if a = 0 then I else 1) (if b = 0 then I else 1)) 2 (volume.restrict O) := by
    fin_cases a <;> fin_cases b
    · simpa using hpairI.2
    · simpa using hpairI.1
    · simpa using hpair1.2
    · simpa using hpair1.1
  have hmp := boundaryComplexCoordinates.measurePreserving.restrict_preimage_emb
    boundaryComplexCoordinates.toHomeomorph.measurableEmbedding O
  apply MemLp.ae_eq ?_ (hraw.comp_measurePreserving hmp)
  filter_upwards [ae_restrict_mem (hO.preimage boundaryComplexCoordinates.continuous).measurableSet]
    with p hp
  exact (boundaryComplexCoordinates_hessian (hH.contDiffAt (hO.mem_nhds hp)) a b).symm

theorem boundaryComplexCoordinates_memWkp_two {O : Set ℂ} (hO : IsOpen O)
    {H : ℂ → Target} (hH : ContDiffOn ℝ ∞ H O)
    (h0 : MemLp H 2 (volume.restrict O))
    (hx : MemLp (fun z => fderiv ℝ H z 1) 2 (volume.restrict O))
    (hy : MemLp (fun z => fderiv ℝ H z I) 2 (volume.restrict O))
    (h1 : MemLp (fun z => fderiv ℝ (complexGradient H) z 1) 2 (volume.restrict O))
    (hI : MemLp (fun z => fderiv ℝ (complexGradient H) z I) 2 (volume.restrict O)) :
    ∀ j : Fin n, MemWkp 2 2
      (fun p => (H (boundaryComplexCoordinates p)) j)
      (boundaryComplexCoordinates ⁻¹' O) := by
  have hpre : IsOpen (boundaryComplexCoordinates ⁻¹' O) :=
    hO.preimage boundaryComplexCoordinates.continuous
  have hs : ContDiffOn ℝ ∞ (H ∘ boundaryComplexCoordinates)
      (boundaryComplexCoordinates ⁻¹' O) :=
    hH.comp boundaryComplexCoordinates.toContinuousLinearEquiv.contDiff.contDiffOn
      (fun _ hp => hp)
  have hmp := boundaryComplexCoordinates.measurePreserving.restrict_preimage_emb
    boundaryComplexCoordinates.toHomeomorph.measurableEmbedding O
  apply vector_memWkp_two_of_classical_hessian hpre hs (h0.comp_measurePreserving hmp)
  · intro i
    have hcol : MemLp (fun z => fderiv ℝ H z (if i = 0 then I else 1))
        2 (volume.restrict O) := by
      by_cases hi : i = 0
      · simpa only [if_pos hi] using hy
      · simpa only [if_neg hi] using hx
    apply MemLp.ae_eq ?_ (hcol.comp_measurePreserving hmp)
    filter_upwards [ae_restrict_mem hpre.measurableSet] with p hp
    rw [fderiv_comp p ((hH.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp))
      boundaryComplexCoordinates.differentiableAt]
    rw [show fderiv ℝ boundaryComplexCoordinates p =
      boundaryComplexCoordinates.toContinuousLinearEquiv.toContinuousLinearMap from
      boundaryComplexCoordinates.toContinuousLinearEquiv.fderiv]
    change fderiv ℝ H (boundaryComplexCoordinates p) (if i = 0 then I else 1) =
      fderiv ℝ H (boundaryComplexCoordinates p)
        (boundaryComplexCoordinates (EuclideanSpace.single i 1))
    rw [boundaryComplexCoordinates_basis]
  · exact boundaryComplexCoordinates_hessian_memLp hO hH h1 hI

end PoincareConjecture.M64.RampTransport
