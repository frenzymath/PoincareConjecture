
import PoincareConjecture.Proofs.M05.Analysis.ODE.LocalFlow.ParametricLinearODE










noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace Poincare.Riemannian.RadialTransport

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


def coefficient (Γ : E → E →L[ℝ] F →L[ℝ] F) (x : E) (t : ℝ) : F →L[ℝ] F :=
  -(Γ (t • x) x)


def solution (Γ : E → E →L[ℝ] F →L[ℝ] F) (v : F) : E → ℝ → F :=
  ODE.LocalFlow.linearODESolution (coefficient Γ) (-2) 2 0 (fun _ => v)


def field (Γ : E → E →L[ℝ] F →L[ℝ] F) (v : F) (x : E) : F :=
  solution Γ v x 1

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma contDiff_coefficient {Γ : E → E →L[ℝ] F →L[ℝ] F}
    (hΓ : ContDiff ℝ ∞ Γ) : ContDiff ℝ ∞ (Function.uncurry (coefficient Γ)) := by
  exact ((hΓ.comp (contDiff_snd.smul contDiff_fst)).clm_apply contDiff_fst).neg

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
@[simp] lemma solution_zero (Γ : E → E →L[ℝ] F →L[ℝ] F) (v : F) (x : E) :
    solution Γ v x 0 = v := by
  exact ODE.LocalFlow.linearODESolution_init _ _ _ _ _ _

omit [FiniteDimensional ℝ E] in
lemma solution_hasDerivAt {Γ : E → E →L[ℝ] F →L[ℝ] F}
    (hΓ : ContDiff ℝ ∞ Γ) (v : F) (x : E) {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (solution Γ v x) (-(Γ (t • x) x (solution Γ v x t))) t := by
  exact ODE.LocalFlow.linearODESolution_hasDerivAt (by norm_num)
    (U := univ) (contDiff_coefficient hΓ).continuous.continuousOn (mem_univ x) ht

lemma contDiffOn_solution {Γ : E → E →L[ℝ] F →L[ℝ] F}
    (hΓ : ContDiff ℝ ∞ Γ) (v : F) :
    ContDiffOn ℝ ∞ (Function.uncurry (solution Γ v)) (univ ×ˢ Ioo (-2 : ℝ) 2) := by
  exact ODE.LocalFlow.linearODESolution_contDiffOn_top (by norm_num) isOpen_univ
    (contDiff_coefficient hΓ).contDiffOn contDiffOn_const

lemma contDiff_field {Γ : E → E →L[ℝ] F →L[ℝ] F}
    (hΓ : ContDiff ℝ ∞ Γ) (v : F) : ContDiff ℝ ∞ (field Γ v) := by
  have harg : ContDiff ℝ ∞ (fun x : E => (x, (1 : ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hcomp := (contDiffOn_solution hΓ v).comp (s := (univ : Set E)) harg.contDiffOn
    (show MapsTo (fun x : E => (x, (1 : ℝ))) univ (univ ×ˢ Ioo (-2 : ℝ) 2)
      from fun _ _ => ⟨trivial, by norm_num⟩)
  exact contDiffOn_univ.mp hcomp

omit [FiniteDimensional ℝ E] in
lemma solution_smul {Γ : E → E →L[ℝ] F →L[ℝ] F}
    (hΓ : ContDiff ℝ ∞ Γ) (v : F) (x : E) {s : ℝ} (hs : |s| ≤ 1)
    {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    solution Γ v (s • x) t = solution Γ v x (s * t) := by
  have htime {r : ℝ} (hr : r ∈ Ioo (-2 : ℝ) 2) : s * r ∈ Ioo (-2 : ℝ) 2 := by
    apply abs_lt.mp
    rw [abs_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hs (abs_nonneg r))
      (by simpa using (abs_lt.mpr hr : |r| < 2))
  apply ODE.LocalFlow.linearODE_unique_on_Ioo (A := coefficient Γ (s • x))
    (a := (-2 : ℝ)) (b := 2) (h₀ := 0)
    (Z₁ := solution Γ v (s • x)) (Z₂ := fun r => solution Γ v x (s * r))
    (by norm_num) _ _ _ _ ht
  · exact ((contDiff_coefficient hΓ).continuous.comp
      (continuous_const.prodMk continuous_id)).continuousOn
  · intro r hr
    exact solution_hasDerivAt hΓ v (s • x) hr
  · intro r hr
    have h := (solution_hasDerivAt hΓ v x (htime hr)).scomp r
      ((hasDerivAt_id r).const_mul s)
    simpa only [coefficient, Function.comp_def, id_eq, neg_apply, map_smul,
      smul_apply, smul_neg, smul_smul, mul_comm, mul_one] using h
  · simp

omit [FiniteDimensional ℝ E] in
lemma field_smul {Γ : E → E →L[ℝ] F →L[ℝ] F}
    (hΓ : ContDiff ℝ ∞ Γ) (v : F) (x : E) {s : ℝ} (hs : |s| ≤ 1) :
    field Γ v (s • x) = solution Γ v x s := by
  simpa only [field, mul_one] using solution_smul hΓ v x hs (t := 1) (by norm_num)


def covariantDerivative (Γ : E → E →L[ℝ] F →L[ℝ] F) (Y : E → F)
    (x u : E) : F := fderiv ℝ Y x u + Γ x u (Y x)

omit [FiniteDimensional ℝ E] in
@[simp] lemma field_zero {Γ : E → E →L[ℝ] F →L[ℝ] F}
    (hΓ : ContDiff ℝ ∞ Γ) (v : F) : field Γ v 0 = v := by
  simpa using field_smul hΓ v (0 : E) (s := 0) (by norm_num)



lemma covariantDerivative_field_radial {Γ : E → E →L[ℝ] F →L[ℝ] F}
    (hΓ : ContDiff ℝ ∞ Γ) (v : F) (u : E) {s : ℝ} (hs : |s| < 1) :
    covariantDerivative Γ (field Γ v) (s • u) u = 0 := by
  have heq : (fun t : ℝ => field Γ v (t • u)) =ᶠ[𝓝 s] solution Γ v u := by
    filter_upwards [isOpen_Ioo.mem_nhds (abs_lt.mp hs)] with t ht
    exact field_smul hΓ v u (abs_lt.mpr ht).le
  have hcurve := ((contDiff_field hΓ v).differentiable (by simp)).differentiableAt
    |>.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const u)
  have hsol := solution_hasDerivAt hΓ v u
    (show s ∈ Ioo (-2 : ℝ) 2 from ⟨by linarith [(abs_lt.mp hs).1],
      by linarith [(abs_lt.mp hs).2]⟩)
  have hder := hcurve.unique (hsol.congr_of_eventuallyEq heq)
  simp only [id_eq, one_smul] at hder
  change fderiv ℝ (field Γ v) (s • u) u =
    -(Γ (s • u) u (solution Γ v u s)) at hder
  rw [← field_smul hΓ v u hs.le] at hder
  exact eq_neg_iff_add_eq_zero.mp hder


lemma covariantDerivative_field_zero {Γ : E → E →L[ℝ] F →L[ℝ] F}
    (hΓ : ContDiff ℝ ∞ Γ) (v : F) (u : E) :
    covariantDerivative Γ (field Γ v) 0 u = 0 := by
  simpa using covariantDerivative_field_radial hΓ v u (s := 0) (by norm_num)

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma covariantDerivative_smul_direction (Γ : E → E →L[ℝ] F →L[ℝ] F)
    (Y : E → F) (x u : E) (c : ℝ) :
    covariantDerivative Γ Y x (c • u) = c • covariantDerivative Γ Y x u := by
  simp only [covariantDerivative, map_smul, smul_apply, smul_add]



lemma covariantDerivative_field_radial_all {Γ : E → E →L[ℝ] F →L[ℝ] F}
    (hΓ : ContDiff ℝ ∞ Γ) (v : F) (u : E) (s : ℝ) :
    covariantDerivative Γ (field Γ v) (s • u) u = 0 := by
  by_cases hs : s = 0
  · simpa only [hs, zero_smul] using covariantDerivative_field_zero hΓ v u
  have h := covariantDerivative_field_radial hΓ v ((2 * s) • u)
    (s := 1 / 2) (by norm_num)
  have heq : (1 / 2 : ℝ) • ((2 * s) • u) = s • u := by
    rw [smul_smul]
    congr 1
    ring
  rw [heq, covariantDerivative_smul_direction] at h
  exact (smul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) hs)

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
lemma contDiff_covariantDerivative {Γ : E → E →L[ℝ] F →L[ℝ] F} {Y : E → F}
    (hΓ : ContDiff ℝ ∞ Γ) (hY : ContDiff ℝ ∞ Y) (u : E) :
    ContDiff ℝ ∞ (fun x => covariantDerivative Γ Y x u) := by
  exact ((hY.fderiv_right (by simp)).clm_apply contDiff_const).add
    ((hΓ.clm_apply contDiff_const).clm_apply hY)



lemma secondCovariantDerivative_field_zero {Γ : E → E →L[ℝ] F →L[ℝ] F}
    (hΓ : ContDiff ℝ ∞ Γ) (v : F) (u : E) :
    covariantDerivative Γ (fun x => covariantDerivative Γ (field Γ v) x u) 0 u = 0 := by
  let Y : E → F := fun x => covariantDerivative Γ (field Γ v) x u
  have hY : ContDiff ℝ ∞ Y := contDiff_covariantDerivative hΓ (contDiff_field hΓ v) u
  have heq : (fun t : ℝ => Y (t • u)) =ᶠ[𝓝 0] fun _ => (0 : F) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by norm_num)]
      with t ht
    exact covariantDerivative_field_radial hΓ v u (abs_lt.mpr ht)
  have hcurve := hY.differentiable (by simp) |>.differentiableAt
    |>.hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const u)
  have hz := hcurve.unique ((hasDerivAt_const (0 : ℝ) (0 : F)).congr_of_eventuallyEq heq)
  have hder : fderiv ℝ Y 0 u = 0 := by simpa using hz
  change fderiv ℝ Y 0 u + Γ 0 u (Y 0) = 0
  rw [hder, show Y 0 = 0 from covariantDerivative_field_zero hΓ v u, map_zero, add_zero]

end Poincare.Riemannian.RadialTransport
