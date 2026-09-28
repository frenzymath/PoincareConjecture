import PoincareConjecture.Proofs.M07.Analysis.Calculus.Diffeomorphism.Perturbation
import PoincareConjecture.Proofs.M25.Topology3D.Plane.AnnularRegularity










set_option autoImplicit false

open Function Set
open scoped ContDiff Manifold Topology NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]




theorem contDiff_diffeomorph_family_symm (D : ℝ → E ≃ₘ[ℝ] E)
    (hD : ContDiff ℝ ∞ (fun p : ℝ × E => D p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : ℝ × E => (D p.1).symm p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  let x := (D p.1).symm p.2
  have hcomp : (fderiv ℝ (D p.1).symm (D p.1 x)).comp
      (fderiv ℝ (D p.1) x) = ContinuousLinearMap.id ℝ E := by
    rw [← fderiv_comp x ((D p.1).symm.contDiff.differentiable (by simp) _)
      ((D p.1).contDiff.differentiable (by simp) _)]
    have heq : (D p.1).symm ∘ D p.1 = id := funext (D p.1).symm_apply_apply
    rw [heq, fderiv_id]
  have hi : Injective (fderiv ℝ (D p.1) x) := by
    intro u v huv
    have h := congrArg (fderiv ℝ (D p.1).symm (D p.1 x)) huv
    simpa only [← ContinuousLinearMap.comp_apply, hcomp,
      ContinuousLinearMap.id_apply] using h
  obtain ⟨e, hsource, he, hInv⟩ := exists_smoothTrack_localInverse
    (fun q : ℝ × E => D q.1 q.2) (p.1, x) hD.contDiffAt hi
  have hep : e (p.1, x) = p := by
    rw [he]
    simp only [x, (D p.1).apply_symm_apply, Prod.mk.eta]
  have hInv' : ContDiffAt ℝ ∞ e.symm p := by
    simpa only [x, (D p.1).apply_symm_apply, Prod.mk.eta] using hInv
  apply (contDiffAt_snd.comp p hInv').congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds (hep ▸ e.map_source hsource)] with y hy
  have hright := e.right_inv hy
  rw [he] at hright
  have htime : (e.symm y).1 = y.1 := by
    simpa only using congrArg (Prod.fst : ℝ × E → ℝ) hright
  have hvalue : D (e.symm y).1 (e.symm y).2 = y.2 := congrArg Prod.snd hright
  rw [htime] at hvalue
  apply (D y.1).injective
  change D y.1 ((D y.1).symm y.2) = D y.1 (e.symm y).2
  rw [(D y.1).apply_symm_apply]
  exact hvalue.symm




theorem exists_smooth_diffeomorph_family_of_fderiv_close_id
    (F : ℝ × E → E) (hF : ContDiff ℝ ∞ F) {c : ℝ≥0} (hc : c < 1)
    (hclose : ∀ t x,
      ‖fderiv ℝ (fun y => F (t, y)) x - ContinuousLinearMap.id ℝ E‖ ≤ c) :
    ∃ D : ℝ → E ≃ₘ[ℝ] E,
      (∀ t x, D t x = F (t, x)) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => D p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (D p.1).symm p.2) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hexists (t : ℝ) : ∃ e : E ≃ₜ E,
      (e : E → E) = (fun x => F (t, x)) ∧
      ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm :=
    Poincare.Analysis.Calculus.exists_smooth_homeomorph_of_fderiv_close_id
      (hF.comp (contDiff_const.prodMk contDiff_id)) hc (hclose t)
  choose e he hs hi using hexists
  let D : ℝ → E ≃ₘ[ℝ] E := fun t =>
    { toEquiv := (e t).toEquiv
      contMDiff_toFun := (hs t).contMDiff
      contMDiff_invFun := (hi t).contMDiff }
  have hvalue (t : ℝ) (x : E) : D t x = F (t, x) := congrFun (he t) x
  have hD : ContDiff ℝ ∞ (fun p : ℝ × E => D p.1 p.2) := by
    have heq : (fun p : ℝ × E => D p.1 p.2) = F := funext fun p => hvalue p.1 p.2
    rw [heq]
    exact hF
  exact ⟨D, hvalue, hD, contDiff_diffeomorph_family_symm D hD⟩

end PoincareConjecture.M25.Topology3D
