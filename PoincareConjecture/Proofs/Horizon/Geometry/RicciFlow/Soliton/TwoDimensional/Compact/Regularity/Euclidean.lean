import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.AlongCurve.Coefficients








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff Bundle Topology
open Bundle Set

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem hessian_eq_fderiv_sub_connectionCoefficient_of_C2 (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ 2 f x) (v w : EuclideanSpace ℝ (Fin n)) :
    D.hessian f x v w = fderiv ℝ (fderiv ℝ f) x v w -
      fderiv ℝ f x (D.connectionCoefficient x v w) := by
  have hfm : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f x := hf.contMDiffAt
  have hw : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (fun y : EuclideanSpace ℝ (Fin n) ↦ TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) y (E := TangentSpace (𝓡 n)) w) x := by
    apply ContMDiffAt.mdifferentiableAt (n := 1) _ (by norm_num)
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using (contMDiffAt_const
      (I := 𝓡 n) (I' := 𝓡 n) (c := w) (x := x) (n := 1))⟩
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := D.metricCompatible.mvfderiv_inner_eq (fun _ => v)
    ((D.contMDiffAt_one_gradient_of_C2 hfm).mdifferentiableAt (by norm_num)) hw
  change mvfderiv (𝓡 n) (fun y => g.inner y (D.gradient f y) w) x v =
    g.inner x (D.connection (D.gradient f) x v) w +
      g.inner x (D.gradient f x) (D.connection (fun _ => w) x v) at h
  simp only [D.inner_gradient] at h
  have hess := D.hessian_eq_inner_connection_gradient_of_C2 hfm v w
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  have heval := hd.clm_apply (hasFDerivAt_const w x)
  simp +instances only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace] at h
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v =
    g.inner x (D.connection (D.gradient f) x v) w +
      fderiv ℝ f x (D.connectionCoefficient x v w) at h
  rw [heval.fderiv] at h
  simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    map_zero, zero_add, ContinuousLinearMap.flip_apply] at h
  linarith


theorem contDiffOn_of_C2_hessian_eq_smooth_mul_metric (D : LeviCivitaData g)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f a : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ 2 f U) (ha : ContDiffOn ℝ ∞ a U)
    (hess : ∀ x ∈ U, ∀ v w,
      D.hessian f x v w = a x * g.inner x v w) :
    ContDiffOn ℝ ∞ f U := by
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ f) U := by
    rw [contDiffOn_infty]
    intro k
    induction k with
    | zero =>
      exact (hf.fderiv_of_isOpen hU (m := 1) (by norm_num)).of_le (by norm_num)
    | succ k ih =>
      rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 by simp,
        contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨?_, by simp, ?_⟩
      · exact (hf.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn
          (by norm_num)
      · apply contDiffOn_clm_apply.mpr
        intro v
        apply contDiffOn_clm_apply.mpr
        intro w
        have ha' := ha.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
        have hg' := (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
        have hΓ' := D.contDiff_connectionCoefficient.of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
        have hright : ContDiffOn ℝ (k : ℕ∞ω)
            (fun x => a x * g.euclideanCoefficients x v w +
              fderiv ℝ f x (D.connectionCoefficient x v w)) U :=
          (ha'.mul ((hg'.contDiffOn.clm_apply contDiffOn_const).clm_apply
          contDiffOn_const)).add (ih.clm_apply
            ((hΓ'.contDiffOn.clm_apply contDiffOn_const).clm_apply contDiffOn_const))
        apply hright.congr
        intro x hx
        have h := D.hessian_eq_fderiv_sub_connectionCoefficient_of_C2
          (hf.contDiffAt (hU.mem_nhds hx)) v w
        rw [hess x hx v w] at h
        change fderiv ℝ (fderiv ℝ f) x v w = _
        dsimp only [RiemannianMetric.euclideanCoefficients]
        exact sub_eq_iff_eq_add.mp h.symm
  rw [contDiffOn_infty_iff_fderiv_of_isOpen hU]
  exact ⟨hf.differentiableOn (by norm_num), hfd⟩

end PoincareConjecture.LeviCivitaData
