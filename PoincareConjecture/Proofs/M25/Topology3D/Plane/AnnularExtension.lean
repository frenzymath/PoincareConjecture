import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import PoincareConjecture.Proofs.M25.Topology3D.Plane.CurveNormal
import PoincareConjecture.Proofs.M25.Topology3D.Plane.RadialCalculus











set_option autoImplicit false

open Set Metric Function
open scoped Manifold ContDiff

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]
variable (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
variable (c : ℝ → sphere (0 : E) 1 → E)



noncomputable def curveAnnularExtension (p : ℝ × E) : E :=
  radialFamilyExtension q0 c p + (‖p.2‖ - 1) •
    curveFamilyNormal o (radialFamilyExtension q0 c)
      (p.1, (unitRadialProjection q0 p.2 : E))



@[simp] theorem curveAnnularExtension_apply_sphere (z : ℝ) (q : sphere (0 : E) 1) :
    curveAnnularExtension o q0 c (z, (q : E)) = c z q := by
  simp [curveAnnularExtension, norm_eq_of_mem_sphere q]



theorem curveAnnularExtension_apply_radial (z : ℝ) (q : sphere (0 : E) 1)
    {r : ℝ} (hr : -1 < r) :
    curveAnnularExtension o q0 c (z, (1 + r) • (q : E)) =
      c z q + r • curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E)) := by
  have hpos : 0 < 1 + r := by linarith
  simp [curveAnnularExtension, radialFamilyExtension_pos_smul q0 c z hpos,
    unitRadialProjection_pos_smul q0 hpos, norm_smul, Real.norm_eq_abs,
    abs_of_pos hpos, norm_eq_of_mem_sphere q]

variable (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
  (fun p : ℝ × sphere (0 : E) 1 => c p.1 p.2))

include hc



theorem contDiffAt_curveAnnularExtension (z : ℝ) (q : sphere (0 : E) 1)
    (hv : curveFamilyVelocity o (radialFamilyExtension q0 c) (z, (q : E)) ≠ 0) :
    ContDiffAt ℝ ∞ (curveAnnularExtension o q0 c) (z, (q : E)) := by
  have hq := ne_zero_of_mem_unit_sphere q
  have hp : (z, (q : E)) ∈ univ ×ˢ ({0} : Set E)ᶜ := ⟨mem_univ _, hq⟩
  have hC := (contDiffOn_radialFamilyExtension q0 c hc).contDiffAt
    ((isOpen_univ.prod isClosed_singleton.isOpen_compl).mem_nhds hp)
  have hP : ContDiffAt ℝ ∞ (fun x : E => (unitRadialProjection q0 x : E)) (q : E) :=
    contDiffAt_unitRadialProjection_coe q0 hq
  have hP' : ContDiffAt ℝ ∞
      (fun p : ℝ × E => (unitRadialProjection q0 p.2 : E)) (z, (q : E)) :=
    ContDiffAt.comp (g := fun x : E => (unitRadialProjection q0 x : E))
      (f := (Prod.snd : ℝ × E → E)) (z, (q : E)) hP contDiffAt_snd
  have hR : ContDiffAt ℝ ∞
      (fun p : ℝ × E => (p.1, (unitRadialProjection q0 p.2 : E))) (z, (q : E)) :=
    contDiffAt_fst.prodMk hP'
  have hN : ContDiffAt ℝ ∞ (curveFamilyNormal o (radialFamilyExtension q0 c))
      (z, (unitRadialProjection q0 (q : E) : E)) := by
    simpa only [unitRadialProjection_apply_coe] using contDiffAt_curveFamilyNormal o hC hv
  have hNR : ContDiffAt ℝ ∞ (fun p : ℝ × E =>
      curveFamilyNormal o (radialFamilyExtension q0 c)
        (p.1, (unitRadialProjection q0 p.2 : E))) (z, (q : E)) :=
    ContDiffAt.comp (g := curveFamilyNormal o (radialFamilyExtension q0 c))
      (f := fun p : ℝ × E => (p.1, (unitRadialProjection q0 p.2 : E)))
      (z, (q : E)) hN hR
  exact hC.add ((((contDiffAt_norm ℝ hq).comp (z, (q : E)) contDiffAt_snd).sub
    contDiffAt_const).smul hNR)




theorem hasFDerivAt_curveAnnularExtension (z : ℝ) (q : sphere (0 : E) 1)
    (hv : curveFamilyVelocity o (radialFamilyExtension q0 c) (z, (q : E)) ≠ 0) :
    HasFDerivAt (fun x => curveAnnularExtension o q0 c (z, x))
      (fderiv ℝ (fun x => radialFamilyExtension q0 c (z, x)) (q : E) +
        (innerSL ℝ (q : E)).smulRight
          (curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E)))) (q : E) := by
  have hq := ne_zero_of_mem_unit_sphere q
  have hp : (z, (q : E)) ∈ univ ×ˢ ({0} : Set E)ᶜ := ⟨mem_univ _, hq⟩
  have hC := (contDiffOn_radialFamilyExtension q0 c hc).contDiffAt
    ((isOpen_univ.prod isClosed_singleton.isOpen_compl).mem_nhds hp)
  have hG := (hC.comp (q : E) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
    (by simp)
  have hN : ContDiffAt ℝ ∞ (curveFamilyNormal o (radialFamilyExtension q0 c))
      (z, (unitRadialProjection q0 (q : E) : E)) := by
    simpa only [unitRadialProjection_apply_coe] using contDiffAt_curveFamilyNormal o hC hv
  have hN' := (hN.comp (q : E)
    (contDiffAt_const.prodMk (contDiffAt_unitRadialProjection_coe q0 hq))).differentiableAt
      (by simp)
  have h := hG.hasFDerivAt.add (((hasFDerivAt_norm_unit q).sub_const 1).smul hN'.hasFDerivAt)
  simpa only [Function.comp_def, Pi.add_def, Pi.smul_def', curveAnnularExtension,
    norm_eq_of_mem_sphere q, sub_self, zero_smul, zero_add,
    unitRadialProjection_apply_coe] using h



theorem fderiv_curveAnnularExtension_directions (z : ℝ) (q : sphere (0 : E) 1)
    (hv : curveFamilyVelocity o (radialFamilyExtension q0 c) (z, (q : E)) ≠ 0) :
    fderiv ℝ (fun x => curveAnnularExtension o q0 c (z, x)) (q : E) (q : E) =
        curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E)) ∧
      fderiv ℝ (fun x => curveAnnularExtension o q0 c (z, x)) (q : E)
          (o.rightAngleRotation (q : E)) =
        curveFamilyVelocity o (radialFamilyExtension q0 c) (z, (q : E)) := by
  rw [(hasFDerivAt_curveAnnularExtension o q0 c hc z q hv).fderiv]
  have hp : (z, (q : E)) ∈ univ ×ˢ ({0} : Set E)ᶜ :=
    ⟨mem_univ _, ne_zero_of_mem_unit_sphere q⟩
  have hC := (contDiffOn_radialFamilyExtension q0 c hc).contDiffAt
    ((isOpen_univ.prod isClosed_singleton.isOpen_compl).mem_nhds hp)
  have hG := (hC.comp (q : E) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
    (by simp)
  constructor
  · change fderiv ℝ (fun x => radialFamilyExtension q0 c (z, x)) (q : E) (q : E) +
      inner ℝ (q : E) (q : E) •
        curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E)) = _
    rw [fderiv_radialFamilyExtension_self q0 c z (q : E) hG,
      real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere q]
    simp
  · change fderiv ℝ (fun x => radialFamilyExtension q0 c (z, x)) (q : E)
        (o.rightAngleRotation (q : E)) + inner ℝ (q : E) (o.rightAngleRotation (q : E)) •
        curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E)) = _
    rw [real_inner_comm (o.rightAngleRotation (q : E)) (q : E),
      o.inner_rightAngleRotation_self, zero_smul, add_zero]
    rfl



theorem bijective_fderiv_curveAnnularExtension (z : ℝ) (q : sphere (0 : E) 1)
    (hv : curveFamilyVelocity o (radialFamilyExtension q0 c) (z, (q : E)) ≠ 0) :
    Bijective (fderiv ℝ (fun x => curveAnnularExtension o q0 c (z, x)) (q : E)) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [show Module.finrank ℝ E = 2 from Fact.out]
    norm_num)
  let D := fderiv ℝ (fun x => curveAnnularExtension o q0 c (z, x)) (q : E)
  let b := o.basisRightAngleRotation (q : E) (ne_zero_of_mem_unit_sphere q)
  let N := curveFamilyNormal o (radialFamilyExtension q0 c) (z, (q : E))
  let V := curveFamilyVelocity o (radialFamilyExtension q0 c) (z, (q : E))
  have hd := fderiv_curveAnnularExtension_directions o q0 c hc z q hv
  have hN : N ≠ 0 := by
    have hn : ‖N‖ = 1 := norm_curveFamilyNormal o _ _ hv
    intro hzero
    simp [hzero] at hn
  have horth : inner ℝ N V = 0 := inner_curveFamilyNormal_velocity o _ _
  have hlin : LinearIndependent ℝ (![N, V] : Fin 2 → E) := by
    apply linearIndependent_of_ne_zero_of_inner_eq_zero
    · intro i
      fin_cases i
      · exact hN
      · exact hv
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · exact horth
      · exact (real_inner_comm N V).trans horth
      · exact (hij rfl).elim
  have himage : D.toLinearMap ∘ b = (![N, V] : Fin 2 → E) := by
    have hb : (b : Fin 2 → E) = ![(q : E), o.rightAngleRotation (q : E)] :=
      o.coe_basisRightAngleRotation (q : E) (ne_zero_of_mem_unit_sphere q)
    funext i
    rw [Function.comp_apply, hb]
    fin_cases i
    · exact hd.1
    · exact hd.2
  have hinj : Injective D.toLinearMap :=
    LinearMap.injective_of_linearIndependent b.span_eq (himage.symm ▸ hlin)
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩




theorem exists_curveAnnularTrack_localInverse (z : ℝ) (q : sphere (0 : E) 1)
    (hv : curveFamilyVelocity o (radialFamilyExtension q0 c) (z, (q : E)) ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ × E) (ℝ × E),
      (z, (q : E)) ∈ e.source ∧
      (∀ p : ℝ × E, e p = (p.1, curveAnnularExtension o q0 c p)) ∧
      ContDiffAt ℝ ∞ e.symm (z, c z q) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [show Module.finrank ℝ E = 2 from Fact.out]
    norm_num)
  let A := curveAnnularExtension o q0 c
  let T : ℝ × E → ℝ × E := fun p => (p.1, A p)
  let L := fderiv ℝ A (z, (q : E))
  let D := fderiv ℝ (fun x => A (z, x)) (q : E)
  let d : E ≃L[ℝ] E := (LinearEquiv.ofBijective D.toLinearMap
    (bijective_fderiv_curveAnnularExtension o q0 c hc z q hv)).toContinuousLinearEquiv
  have hA : ContDiffAt ℝ ∞ A (z, (q : E)) :=
    contDiffAt_curveAnnularExtension o q0 c hc z q hv
  have hAD : HasFDerivAt A L (z, (q : E)) := (hA.differentiableAt (by simp)).hasFDerivAt
  have hsp : L.comp (ContinuousLinearMap.inr ℝ ℝ E) = (d : E →L[ℝ] E) := by
    have h := hAD.comp (q : E) (hasFDerivAt_prodMk_right z (q : E))
    exact h.fderiv.symm
  let B : (ℝ × E) ≃L[ℝ] (ℝ × E) :=
    (ContinuousLinearEquiv.refl ℝ ℝ).skewProd d (L.comp (ContinuousLinearMap.inl ℝ ℝ E))
  have hB : (B : ℝ × E →L[ℝ] ℝ × E) = (ContinuousLinearMap.fst ℝ ℝ E).prod L := by
    apply ContinuousLinearMap.ext
    intro p
    apply Prod.ext
    · rfl
    · change d p.2 + L (p.1, 0) = L p
      have hd : d p.2 = L (0, p.2) :=
        (congrArg (fun f : E →L[ℝ] E => f p.2) hsp).symm
      rw [hd, ← map_add]
      simp
  have hTD : HasFDerivAt T (B : ℝ × E →L[ℝ] ℝ × E) (z, (q : E)) := by
    rw [hB]
    exact hasFDerivAt_fst.prodMk hAD
  have hT : ContDiffAt ℝ ∞ T (z, (q : E)) := contDiffAt_fst.prodMk hA
  let e := hT.toOpenPartialHomeomorph T hTD (by simp)
  refine ⟨e, hT.mem_toOpenPartialHomeomorph_source hTD (by simp), ?_, ?_⟩
  · intro p
    rfl
  · have hInv := hT.to_localInverse hTD (by simp)
    change ContDiffAt ℝ ∞ e.symm (T (z, (q : E))) at hInv
    simpa only [T, A, curveAnnularExtension_apply_sphere] using hInv

end PoincareConjecture.M25.Topology3D
