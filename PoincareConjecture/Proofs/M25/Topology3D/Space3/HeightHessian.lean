import PoincareConjecture.Proofs.M25.Topology3D.Space3.NormalPlane
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

variable {V W E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem fderiv_apply_fixedVector (A : V → W →L[ℝ] E) {x : V}
    (hA : DifferentiableAt ℝ A x) (a : V) (b : W) :
    fderiv ℝ (fun y => A y b) x a = fderiv ℝ A x a b := by
  rw [fderiv_clm_apply hA (differentiableAt_const b)]
  simp

theorem unit_normal_fderiv_orthogonal (n : V → E) {U : Set V}
    (hU : IsOpen U) (hn : ContDiffOn ℝ ∞ n U)
    (hnorm : ∀ y ∈ U, ‖n y‖ = 1) {x : V} (hx : x ∈ U) (a : V) :
    ⟪n x, fderiv ℝ n x a⟫_ℝ = 0 := by
  have hd := (hn.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have heq : (fun y => ⟪n y, n y⟫_ℝ) =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [real_inner_self_eq_norm_sq, hnorm y hy, one_pow]
  have hzero := congrArg (fun A : V →L[ℝ] ℝ => A a)
    (heq.fderiv_eq.trans (fderiv_const_apply (1 : ℝ)))
  rw [fderiv_inner_apply ℝ hd hd a] at hzero
  change ⟪n x, fderiv ℝ n x a⟫_ℝ + ⟪fderiv ℝ n x a, n x⟫_ℝ = 0 at hzero
  linarith [real_inner_comm (n x) (fderiv ℝ n x a)]

theorem normal_second_fderiv (e n : V → E) {U : Set V}
    (hU : IsOpen U) (he : ContDiffOn ℝ ∞ e U) (hn : ContDiffOn ℝ ∞ n U)
    (horth : ∀ y ∈ U, ∀ b : V, ⟪n y, fderiv ℝ e y b⟫_ℝ = 0)
    {x : V} (hx : x ∈ U) (a b : V) :
    ⟪n x, fderiv ℝ (fderiv ℝ e) x a b⟫_ℝ =
      -⟪fderiv ℝ n x a, fderiv ℝ e x b⟫_ℝ := by
  have hdn := (hn.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hde := ((he.fderiv_of_isOpen hU (by simp) :
    ContDiffOn ℝ ∞ (fderiv ℝ e) U).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have heq : (fun y => ⟪n y, fderiv ℝ e y b⟫_ℝ) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact horth y hy b
  have hzero := congrArg (fun A : V →L[ℝ] ℝ => A a)
    (heq.fderiv_eq.trans (fderiv_const_apply (0 : ℝ)))
  rw [fderiv_inner_apply ℝ hdn (hde.clm_apply (differentiableAt_const b)) a,
    fderiv_apply_fixedVector (fderiv ℝ e) hde a b] at hzero
  change ⟪n x, fderiv ℝ (fderiv ℝ e) x a b⟫_ℝ +
    ⟪fderiv ℝ n x a, fderiv ℝ e x b⟫_ℝ = 0 at hzero
  linarith

theorem height_second_fderiv (e : V → E) {U : Set V}
    (hU : IsOpen U) (he : ContDiffOn ℝ ∞ e U) (u : E)
    {x : V} (hx : x ∈ U) (a b : V) :
    fderiv ℝ (fderiv ℝ (fun y => ⟪u, e y⟫_ℝ)) x a b =
      ⟪u, fderiv ℝ (fderiv ℝ e) x a b⟫_ℝ := by
  let h : V → ℝ := fun y => ⟪u, e y⟫_ℝ
  have hh : ContDiffOn ℝ ∞ h U := contDiffOn_const.inner ℝ he
  have hde := ((he.fderiv_of_isOpen hU (by simp) :
    ContDiffOn ℝ ∞ (fderiv ℝ e) U).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hdh := ((hh.fderiv_of_isOpen hU (by simp) :
    ContDiffOn ℝ ∞ (fderiv ℝ h) U).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have heq : (fun y => fderiv ℝ h y b) =ᶠ[𝓝 x]
      fun y => ⟪u, fderiv ℝ e y b⟫_ℝ := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hyde := (he.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
    change fderiv ℝ (fun y => ⟪u, e y⟫_ℝ) y b = _
    rw [fderiv_inner_apply ℝ (differentiableAt_const u) hyde b]
    simp
  have hdiff := congrArg (fun A : V →L[ℝ] ℝ => A a) heq.fderiv_eq
  rw [fderiv_apply_fixedVector (fderiv ℝ h) hdh a b,
    fderiv_inner_apply ℝ (differentiableAt_const u)
      (hde.clm_apply (differentiableAt_const b)) a,
    fderiv_apply_fixedVector (fderiv ℝ e) hde a b] at hdiff
  simpa using hdiff

variable [FiniteDimensional ℝ E]

theorem height_hessian_kernel_iff (e n : V → E) {U : Set V}
    (hU : IsOpen U) (he : ContDiffOn ℝ ∞ e U) (hn : ContDiffOn ℝ ∞ n U)
    (hnorm : ∀ y ∈ U, ‖n y‖ = 1)
    (horth : ∀ y ∈ U, ∀ b : V, ⟪n y, fderiv ℝ e y b⟫_ℝ = 0)
    {x : V} (hx : x ∈ U) (hde : Function.Injective (fderiv ℝ e x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ V + 1)
    (σ : ℝ) (hσ : σ ≠ 0) (a : V) :
    fderiv ℝ (fderiv ℝ (fun y => ⟪σ • n x, e y⟫_ℝ)) x a = 0 ↔
      fderiv ℝ n x a = 0 := by
  have hnx : n x ≠ 0 := by
    intro hz
    have h := hnorm x hx
    rw [hz, norm_zero] at h
    exact zero_ne_one h
  have hrange := range_eq_normal_perp (fderiv ℝ e x) hde hdim (n x) hnx (horth x hx)
  have hformula (b : V) :
      fderiv ℝ (fderiv ℝ (fun y => ⟪σ • n x, e y⟫_ℝ)) x a b =
        -σ * ⟪fderiv ℝ n x a, fderiv ℝ e x b⟫_ℝ := by
    rw [height_second_fderiv e hU he (σ • n x) hx a b, real_inner_smul_left,
      normal_second_fderiv e n hU he hn horth hx a b]
    ring
  constructor
  · intro ha
    have hpair (b : V) : ⟪fderiv ℝ n x a, fderiv ℝ e x b⟫_ℝ = 0 := by
      have h := hformula b
      rw [ha, zero_apply] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (neg_ne_zero.mpr hσ)
    have hmem : fderiv ℝ n x a ∈ (fderiv ℝ e x).range := by
      rw [hrange]
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        (unit_normal_fderiv_orthogonal n hU hn hnorm hx a)
    obtain ⟨b, hb⟩ := hmem
    change fderiv ℝ e x b = fderiv ℝ n x a at hb
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    simpa only [hb] using hpair b
  · intro ha
    apply ContinuousLinearMap.ext
    intro b
    rw [hformula, ha, inner_zero_left, mul_zero, zero_apply]

theorem height_hessian_injective (e n : V → E) {U : Set V}
    (hU : IsOpen U) (he : ContDiffOn ℝ ∞ e U) (hn : ContDiffOn ℝ ∞ n U)
    (hnorm : ∀ y ∈ U, ‖n y‖ = 1)
    (horth : ∀ y ∈ U, ∀ b : V, ⟪n y, fderiv ℝ e y b⟫_ℝ = 0)
    {x : V} (hx : x ∈ U) (hde : Function.Injective (fderiv ℝ e x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ V + 1)
    (hdn : Function.Injective (fderiv ℝ n x)) (σ : ℝ) (hσ : σ ≠ 0) :
    Function.Injective (fderiv ℝ (fderiv ℝ (fun y => ⟪σ • n x, e y⟫_ℝ)) x) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  exact hdn ((height_hessian_kernel_iff e n hU he hn hnorm horth hx hde hdim σ hσ a).mp ha
    |>.trans (map_zero _).symm)

end PoincareConjecture.M25.Topology3D
