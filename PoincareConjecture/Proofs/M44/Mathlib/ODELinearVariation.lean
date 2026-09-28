import PoincareConjecture.Proofs.M44.Mathlib.ODEFirstVariation
import PoincareConjecture.Proofs.M44.Mathlib.CompactSmoothConvergence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

universe u

section LinearVariation

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]



noncomputable def linearVariationalField (F : E → E) (z : E × (P →L[ℝ] E)) :
    E × (P →L[ℝ] E) := (F z.1, (fderiv ℝ F z.1).comp z.2)



noncomputable def linearVariation (γ : P × ℝ → E) (z : P × ℝ) : E × (P →L[ℝ] E) :=
  (γ z, fderiv ℝ (fun p => γ (p, z.2)) z.1)


theorem ContDiff.linearVariationalField {F : E → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (linearVariationalField (P := P) F) :=
  (hF.comp contDiff_fst).prodMk
    (((hF.fderiv_right (m := ∞) (by simp)).comp contDiff_fst).clm_comp contDiff_snd)



theorem ContDiffAt.linearVariationalField {F : E → E} {z : E × (P →L[ℝ] E)}
    (hF : ContDiffAt ℝ ∞ F z.1) :
    ContDiffAt ℝ ∞ (linearVariationalField F) z :=
  (hF.comp z contDiffAt_fst).prodMk
    (((hF.fderiv_right (by simp)).comp z contDiffAt_fst).clm_comp contDiffAt_snd)



theorem ContDiffAt.linearVariation {γ : P × ℝ → E} {z : P × ℝ}
    (hγ : ContDiffAt ℝ ∞ γ z) : ContDiffAt ℝ ∞ (linearVariation γ) z := by
  have hfull : ContDiffAt ℝ ∞
      (fun w => (γ w, (fderiv ℝ γ w).comp (ContinuousLinearMap.inl ℝ P ℝ))) z :=
    hγ.prodMk ((hγ.fderiv_right (m := ∞) (by simp)).clm_comp contDiffAt_const)
  have hnear : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ γ w :=
    ((hγ.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).eventually (by decide)).mono
      fun _ hw => hw.differentiableAt one_ne_zero
  apply hfull.congr_of_eventuallyEq
  filter_upwards [hnear] with w hw
  refine Prod.ext rfl ?_
  have hinc : HasFDerivAt (fun q : P => (q, w.2)) (ContinuousLinearMap.inl ℝ P ℝ) w.1 :=
    (hasFDerivAt_id w.1).prodMk (hasFDerivAt_const w.2 w.1)
  exact (hw.hasFDerivAt.comp w.1 hinc).fderiv




theorem hasDerivAt_linearVariation
    {F : E → E} {γ : P × ℝ → E} {p : P} {t : ℝ}
    (hγ : ContDiffAt ℝ ∞ γ (p, t))
    (hode : ∀ᶠ q in 𝓝 p, HasDerivAt (fun s => γ (q, s)) (F (γ (q, t))) t)
    (hF : DifferentiableAt ℝ F (γ (p, t))) :
    HasDerivAt (fun s => linearVariation γ (p, s))
      (linearVariationalField F (linearVariation γ (p, t))) t := by
  let J : ℝ → P →L[ℝ] E := fun s => fderiv ℝ (fun q => γ (q, s)) p
  have hJs : ContDiffAt ℝ ∞ J t :=
    (hγ.linearVariation.comp t (contDiffAt_const.prodMk contDiffAt_id)).snd
  have hJ : HasDerivAt J (deriv J t) t := (hJs.differentiableAt (by simp)).hasDerivAt
  have hder : deriv J t = (fderiv ℝ F (γ (p, t))).comp (J t) := by
    ext v
    have heval := hJ.clm_apply (hasDerivAt_const t v)
    have hactual := (hasDerivAt_first_variation hγ hode hF v).snd
    have heq := heval.unique hactual
    simpa only [ContinuousLinearMap.map_zero, add_zero, firstVariationalField,
      ContinuousLinearMap.comp_apply, J] using heq
  exact hode.self_of_nhds.prodMk (hJ.congr_deriv hder)

end LinearVariation




theorem CompactSmoothConvergenceOn.linearVariationalField
    {E P : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {ι : Type*} {l : Filter ι} {Fseq : ι → E → E} {F : E → E}
    (h : CompactSmoothConvergenceOn Fseq F l univ) :
    CompactSmoothConvergenceOn (fun i => linearVariationalField (P := P) (Fseq i))
      (linearVariationalField F) l univ := by
  let X := E × (P →L[ℝ] E)
  let L := ContinuousLinearMap.fst ℝ E (P →L[ℝ] E)
  have hpair : CompactSmoothConvergenceOn
      (fun i (z : X) => (Fseq i z.1, _root_.fderiv ℝ (Fseq i) z.1))
      (fun z : X => (F z.1, _root_.fderiv ℝ F z.1)) l univ := by
    simpa only [preimage_univ, Function.comp_def, X, L, ContinuousLinearMap.coe_fst'] using
      (h.prodMk h.fderiv).comp_continuousLinearMap L
  have hlin : CompactSmoothConvergenceOn
      (fun _ : ι => (Prod.snd : X → P →L[ℝ] E)) Prod.snd l univ :=
    CompactSmoothConvergenceOn.constant isOpen_univ contDiff_snd.contDiffOn
  let H (z : (E × (E →L[ℝ] E)) × (P →L[ℝ] E)) : X := (z.1.1, z.1.2.comp z.2)
  have hH : ContDiff ℝ ∞ H := by
    exact (contDiff_fst.comp contDiff_fst).prodMk
      ((contDiff_snd.comp contDiff_fst).clm_comp contDiff_snd)
  exact (hpair.prodMk hlin).comp_smooth isOpen_univ hH.contDiffOn (fun _ _ => mem_univ _)
