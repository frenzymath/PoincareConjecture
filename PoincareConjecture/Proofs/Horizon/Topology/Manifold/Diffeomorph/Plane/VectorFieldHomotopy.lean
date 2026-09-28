import PoincareConjecture.Proofs.Horizon.Analysis.Complex.SmoothLogarithm
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Jordan.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.PlaneDiffeomorph

private abbrev E2 := EuclideanSpace ℝ (Fin 2)

theorem exists_nonvanishing_homotopy
    {V : E2 → E2} (hV : ContDiff ℝ ∞ V) (hne : ∀ x, V x ≠ 0)
    {v : E2} (hv : v ≠ 0) {K : Set E2} (hK : IsCompact K)
    (hfix : ∀ x, x ∉ K → V x = v) :
    ∃ H : ℝ × E2 → E2, ContDiff ℝ ∞ H ∧
      (∀ t x, H (t, x) ≠ 0) ∧
      (∀ x, H (0, x) = v) ∧ (∀ x, H (1, x) = V x) ∧
      ∃ R > 0, K ⊆ closedBall (0 : E2) R ∧
        ∀ t x, R < ‖x‖ → H (t, x) = v := by
  let e : E2 ≃L[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv
  have hev : e v ≠ 0 := by simpa using hv
  let f : E2 → ℂ := fun x => e (V x) / e v
  have hf : ContDiff ℝ ∞ f := (e.contDiff.comp hV).div_const _
  have hfne (x : E2) : f x ≠ 0 := div_ne_zero (by simpa using hne x) hev
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  have hU := Poincare.Topology.Plane.Jordan.isConnected_compl_closedBall hR.le
  have hUf (x : E2) (hx : R < ‖x‖) : f x = 1 := by
    have hxK : x ∉ K := fun h => (hKR x h).not_gt hx
    simp [f, hfix x hxK, hev]
  obtain ⟨L, hL, hexp, hLfix⟩ :=
    Poincare.Complex.exists_contDiff_logarithm_eq_zero hf hfne
      hU.isPreconnected hU.nonempty hUf
  let H : ℝ × E2 → E2 := fun z => e.symm (Complex.exp (z.1 • L z.2) * e v)
  refine ⟨H, ?_, ?_, ?_, ?_, R, hR, ?_, ?_⟩
  · exact e.symm.contDiff.comp
      (((contDiff_fst.smul (hL.comp contDiff_snd)).cexp).mul contDiff_const)
  · intro t x h
    have h' : Complex.exp (t • L x) * e v = 0 := by
      apply e.symm.injective
      simpa only [H, map_zero] using h
    exact mul_ne_zero (Complex.exp_ne_zero _) hev h'
  · intro x
    simp [H]
  · intro x
    simp [H, hexp, f, div_mul_cancel₀ _ hev]
  · intro x hx
    simpa only [mem_closedBall, dist_zero_right] using hKR x hx
  · intro t x hx
    simp [H, hLfix x hx]

theorem exists_pushforward_homotopy
    (g : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {K : Set E2} (hK : IsCompact K) (hfix : ∀ x, x ∉ K → g x = x)
    {v : E2} (hv : v ≠ 0) :
    ∃ H : ℝ × E2 → E2, ContDiff ℝ ∞ H ∧
      (∀ t x, H (t, x) ≠ 0) ∧
      (∀ x, H (0, x) = v) ∧
      (∀ x, H (1, x) = fderiv ℝ g (g.symm x) v) ∧
      ∃ R > 0, K ⊆ closedBall (0 : E2) R ∧
        ∀ t x, R < ‖x‖ → H (t, x) = v := by
  have hg : ContDiff ℝ ∞ g := g.contMDiff.contDiff
  have hgi : ContDiff ℝ ∞ g.symm := g.symm.contMDiff.contDiff
  apply exists_nonvanishing_homotopy
    (((hg.fderiv_right (by simp)).comp hgi).clm_apply contDiff_const) _ hv hK
  · intro x hx
    have hix : g.symm x = x := by
      apply g.injective
      change g (g.symm x) = g x
      rw [g.apply_symm_apply, hfix x hx]
    have heq : (g : E2 → E2) =ᶠ[nhds x] id := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
      exact hfix y hy
    change fderiv ℝ g (g.symm x) v = v
    rw [hix, heq.fderiv_eq, fderiv_id]
    rfl
  · intro x hx
    have hcomp : (g.symm : E2 → E2) ∘ g = id := funext g.symm_apply_apply
    have hd : (fderiv ℝ g.symm (g (g.symm x))).comp
        (fderiv ℝ g (g.symm x)) = ContinuousLinearMap.id ℝ E2 := by
      rw [← fderiv_comp (g.symm x)
        (hgi.differentiable (by simp)).differentiableAt
        (hg.differentiable (by simp)).differentiableAt, hcomp, fderiv_id]
    have heq := congrArg (fun A : E2 →L[ℝ] E2 => A v) hd
    change fderiv ℝ g (g.symm x) v = 0 at hx
    exact hv (by simpa only [ContinuousLinearMap.comp_apply, hx, map_zero,
      ContinuousLinearMap.id_apply] using heq.symm)

end Poincare.Manifold.PlaneDiffeomorph
