import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Jacobi.ParallelFrame












noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.CoordinateExponential

open ConnectionVariation

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem covDerivAlong_variation_of_parallel
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {q V : P → E} {p : P}
    (hq : ContDiffAt ℝ 2 q p) (hV : ContDiffAt ℝ 2 V p)
    (hΓ : DifferentiableAt ℝ Γ (q p)) (t s : P)
    (hpar : covDerivAlong Γ q V t =ᶠ[𝓝 p] fun _ => 0) :
    covDerivAlong Γ q (covDerivAlong Γ q V s) t p =
      christoffelCurvature Γ (q p) (fderiv ℝ q p t) (fderiv ℝ q p s) (V p) := by
  have h := covDerivAlong_comm hq hV hΓ t s
  rw [covDerivAlong_congr Γ q hpar s, covDerivAlong_zero, sub_zero] at h
  exact h



theorem fderiv_inverse_transport_apply [CompleteSpace E]
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {q V : P → E}
    {T : P → E →L[ℝ] E} {p d : P}
    (hV : DifferentiableAt ℝ V p)
    (hT : DifferentiableAt ℝ T p) (hTi : (T p).IsInvertible)
    (hpar : fderiv ℝ T p d = -(Γ (q p) (fderiv ℝ q p d)).comp (T p)) :
    fderiv ℝ (fun z => (T z).inverse (V z)) p d =
      (T p).inverse (covDerivAlong Γ q V d p) := by
  let Y : P → E := fun z => (T z).inverse (V z)
  have hi : DifferentiableAt ℝ (fun z => (T z).inverse) p :=
    ((hTi.contDiffAt_map_inverse (n := 1)).differentiableAt (by norm_num)).comp p hT
  have hY : DifferentiableAt ℝ Y p := hi.clm_apply hV
  have hnear : ∀ᶠ z in 𝓝 p, (T z).IsInvertible := by
    obtain ⟨e, he⟩ := hTi
    have h := e.nhds
    rw [he] at h
    exact hT.continuousAt.preimage_mem_nhds h
  have heq : (fun z => T z (Y z)) =ᶠ[𝓝 p] V := by
    filter_upwards [hnear] with z hz
    exact hz.self_apply_inverse _
  have hd := (hT.hasFDerivAt.clm_apply hY.hasFDerivAt).fderiv
  have hval := congrArg (fun L : P →L[ℝ] E => L d) (heq.fderiv_eq.symm.trans hd)
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, hpar, neg_apply,
    Y, hTi.self_apply_inverse] at hval
  apply hTi.injective
  rw [hTi.self_apply_inverse]
  change T p (fderiv ℝ Y p d) = _
  rw [covDerivAlong, hval]
  abel



theorem fderiv_inverse_transport_variation [CompleteSpace E]
    {Γ : E → E →L[ℝ] E →L[ℝ] E} {q V : P → E}
    {T : P → E →L[ℝ] E} {p : P}
    (hq : ContDiffAt ℝ ∞ q p) (hV : ContDiffAt ℝ ∞ V p)
    (hΓ : ContDiffAt ℝ ∞ Γ (q p))
    (hT : DifferentiableAt ℝ T p) (hTi : (T p).IsInvertible)
    (t s : P)
    (hparT : fderiv ℝ T p t = -(Γ (q p) (fderiv ℝ q p t)).comp (T p))
    (hparV : covDerivAlong Γ q V t =ᶠ[𝓝 p] fun _ => 0) :
    fderiv ℝ (fun z => (T z).inverse (covDerivAlong Γ q V s z)) p t =
      (T p).inverse
        (christoffelCurvature Γ (q p) (fderiv ℝ q p t) (fderiv ℝ q p s) (V p)) := by
  rw [fderiv_inverse_transport_apply
    ((contDiffAt_covDerivAlong hΓ hq hV s).differentiableAt (by simp)) hT hTi hparT]
  rw [covDerivAlong_variation_of_parallel
    (hq.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hV.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hΓ.differentiableAt (by simp)) t s hparV]



theorem fderiv_inverse_metric_transport_variation [CompleteSpace E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {q V : P → E}
    {T : P → E →L[ℝ] E} {p : P}
    (hq : ContDiffAt ℝ ∞ q p) (hV : ContDiffAt ℝ ∞ V p)
    (hB : ContDiffAt ℝ ∞ B (q p)) (hBi : (B (q p)).IsInvertible)
    (hT : DifferentiableAt ℝ T p) (hTi : (T p).IsInvertible)
    (t s : P)
    (hparT : fderiv ℝ T p t =
      -(christoffelBilinear B (q p) (fderiv ℝ q p t)).comp (T p))
    (hparV : covDerivAlong (christoffelBilinear B) q V t =ᶠ[𝓝 p] fun _ => 0) :
    fderiv ℝ (fun z => (T z).inverse
      (covDerivAlong (christoffelBilinear B) q V s z)) p t =
      (T p).inverse
        (coordinateCurvature B (q p) (fderiv ℝ q p t) (fderiv ℝ q p s) (V p)) := by
  have hΓ := contDiffAt_christoffelBilinear hB hBi
  rw [coordinateCurvature_eq_christoffelCurvature (hΓ.differentiableAt (by simp))]
  exact fderiv_inverse_transport_variation hq hV hΓ hT hTi t s hparT hparV

end PoincareConjecture.CoordinateExponential
