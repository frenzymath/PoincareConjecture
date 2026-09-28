import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.HarmonicMinimum
import PoincareConjecture.Definitions.M64Annulus

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter InnerProductSpace
open scoped Topology ContDiff

namespace PoincareConjecture

def m64ModulusSourceDilation (r : ℝ) (hr : r ≠ 0) : LoopPlane ≃L[ℝ] LoopPlane where
  toFun p := annulusPoint (r * p 0) (p 1)
  invFun p := annulusPoint (r⁻¹ * p 0) (p 1)
  map_add' p q := by
    ext i
    fin_cases i <;> simp [annulusPoint, mul_add]
  map_smul' c p := by
    ext i
    fin_cases i <;> simp [annulusPoint, mul_left_comm]
  left_inv p := by
    ext i
    fin_cases i <;> simp [annulusPoint, hr]
  right_inv p := by
    ext i
    fin_cases i <;> simp [annulusPoint, hr]
  continuous_toFun := by unfold annulusPoint; fun_prop
  continuous_invFun := by unfold annulusPoint; fun_prop

theorem m64ModulusSourceDilation_hessian (r : ℝ) (hr : r ≠ 0)
    (f : LoopPlane → ℝ) (p v w : LoopPlane) :
    fderiv ℝ (fderiv ℝ (f ∘ m64ModulusSourceDilation r hr)) p v w =
      fderiv ℝ (fderiv ℝ f) (m64ModulusSourceDilation r hr p)
        (m64ModulusSourceDilation r hr v) (m64ModulusSourceDilation r hr w) := by
  let L := m64ModulusSourceDilation r hr
  have hi := L.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (show L p ∈ (univ : Set LoopPlane) from mem_univ _) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at hi
  have hv := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => LoopPlane) ℝ =>
    T ![v, w]) hi
  simpa only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, ContinuousLinearEquiv.coe_coe] using hv

theorem m64ModulusSourceDilation_laplacian (r : ℝ) (hr : r ≠ 0)
    (f : LoopPlane → ℝ) (p : LoopPlane) :
    Laplacian.laplacian (f ∘ m64ModulusSourceDilation r hr) p =
      r * (r * fderiv ℝ (fderiv ℝ f) (m64ModulusSourceDilation r hr p)
        (EuclideanSpace.single (0 : Fin 2) 1) (EuclideanSpace.single (0 : Fin 2) 1) +
      r⁻¹ * fderiv ℝ (fderiv ℝ f) (m64ModulusSourceDilation r hr p)
        (EuclideanSpace.single (1 : Fin 2) 1) (EuclideanSpace.single (1 : Fin 2) 1)) := by
  let e0 : LoopPlane := EuclideanSpace.single (0 : Fin 2) 1
  let e1 : LoopPlane := EuclideanSpace.single (1 : Fin 2) 1
  have hL0 : m64ModulusSourceDilation r hr e0 = r • e0 := by
    ext i
    fin_cases i <;> simp [e0, m64ModulusSourceDilation, annulusPoint]
  have hL1 : m64ModulusSourceDilation r hr e1 = e1 := by
    ext i
    fin_cases i <;> simp [e1, m64ModulusSourceDilation, annulusPoint]
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis
    (f ∘ m64ModulusSourceDilation r hr) (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp only [Fin.sum_univ_two, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, EuclideanSpace.basisFun_apply,
    m64ModulusSourceDilation_hessian]
  change fderiv ℝ (fderiv ℝ f) (m64ModulusSourceDilation r hr p)
      (m64ModulusSourceDilation r hr e0) (m64ModulusSourceDilation r hr e0) +
    fderiv ℝ (fderiv ℝ f) (m64ModulusSourceDilation r hr p)
      (m64ModulusSourceDilation r hr e1) (m64ModulusSourceDilation r hr e1) = _
  rw [hL0, hL1]
  simp only [map_smul, smul_apply, smul_eq_mul]
  field_simp
  ring

theorem m64ModulusHarmonicAt_eventually_eq_of_isLocalMin
    {r : ℝ} (hr : 0 < r) {f : LoopPlane → ℝ} {p : LoopPlane}
    (hf : ContDiffAt ℝ 2 f p)
    (heq : ∀ᶠ q in 𝓝 p,
      r * fderiv ℝ (fderiv ℝ f) q (EuclideanSpace.single (0 : Fin 2) 1)
        (EuclideanSpace.single (0 : Fin 2) 1) +
      r⁻¹ * fderiv ℝ (fderiv ℝ f) q (EuclideanSpace.single (1 : Fin 2) 1)
        (EuclideanSpace.single (1 : Fin 2) 1) = 0)
    (hmin : IsLocalMin f p) : f =ᶠ[𝓝 p] fun _ => f p := by
  let L := m64ModulusSourceDilation r hr.ne'
  let q := L.symm p
  have hLp : L q = p := L.apply_symm_apply p
  have hh : HarmonicAt (f ∘ L) q := by
    refine ⟨(hLp.symm ▸ hf).comp q L.contDiff.contDiffAt, ?_⟩
    have hback := L.continuous.continuousAt.tendsto.eventually (hLp.symm ▸ heq)
    filter_upwards [hback] with y hy
    change Laplacian.laplacian (f ∘ L) y = 0
    rw [m64ModulusSourceDilation_laplacian, hy, mul_zero]
  have hm : IsLocalMin (f ∘ L) q := by
    have hm' := L.continuous.continuousAt.tendsto.eventually (hLp.symm ▸ hmin)
    exact hm'
  have hlocal := m64PlaneHarmonicAt_eventually_eq_of_isLocalMin hh hm
  have hback := L.symm.continuous.continuousAt.tendsto.eventually hlocal
  change ∀ᶠ x in 𝓝 p, f x = f p
  simpa only [Function.comp_apply, hLp, L.apply_symm_apply] using hback

theorem m64ModulusHarmonic_eqOn_of_minimum
    {r : ℝ} (hr : 0 < r) {f : LoopPlane → ℝ} {U : Set LoopPlane}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hf : ContDiffOn ℝ 2 f U)
    (heq : ∀ q ∈ U,
      r * fderiv ℝ (fderiv ℝ f) q (EuclideanSpace.single (0 : Fin 2) 1)
        (EuclideanSpace.single (0 : Fin 2) 1) +
      r⁻¹ * fderiv ℝ (fderiv ℝ f) q (EuclideanSpace.single (1 : Fin 2) 1)
        (EuclideanSpace.single (1 : Fin 2) 1) = 0)
    {p : LoopPlane} (hp : p ∈ U) (hmin : ∀ q ∈ U, f p ≤ f q) :
    EqOn f (fun _ => f p) U := by
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  have hc : Continuous (fun q : U => f q) :=
    continuousOn_iff_continuous_domRestrict.mp hf.continuousOn
  have hclosed : IsClosed {q : U | f q = f p} := isClosed_eq hc continuous_const
  have hopen : IsOpen {q : U | f q = f p} := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    have hm : IsLocalMin f q := by
      filter_upwards [hU.mem_nhds q.property] with y hy
      exact hq.symm ▸ hmin y hy
    have he : ∀ᶠ y in 𝓝 (q : LoopPlane),
        r * fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.single (0 : Fin 2) 1)
          (EuclideanSpace.single (0 : Fin 2) 1) +
        r⁻¹ * fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.single (1 : Fin 2) 1)
          (EuclideanSpace.single (1 : Fin 2) 1) = 0 := by
      filter_upwards [hU.mem_nhds q.property] with y hy
      exact heq y hy
    have hconst := m64ModulusHarmonicAt_eventually_eq_of_isLocalMin hr
      (hf.contDiffAt (hU.mem_nhds q.property)) he hm
    have hback := continuous_subtype_val.continuousAt.tendsto.eventually hconst
    filter_upwards [hback] with y hy
    exact hy.trans hq
  have hall := (show IsClopen {q : U | f q = f p} from ⟨hclosed, hopen⟩).eq_univ
    (show ({q : U | f q = f p} : Set U).Nonempty from ⟨⟨p, hp⟩, rfl⟩)
  intro q hq
  exact (Set.eq_univ_iff_forall.mp hall) ⟨q, hq⟩

end PoincareConjecture
