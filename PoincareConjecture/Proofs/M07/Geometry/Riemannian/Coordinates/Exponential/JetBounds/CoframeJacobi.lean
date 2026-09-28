import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.ConnectionKernel
import PoincareConjecture.Proofs.M07.Analysis.ODE.Jacobi.MatrixParameterBounds

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateExponential

open ConnectionVariation Poincare.Riemannian.RadialTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

private theorem fderiv_time_radial_parameter (z d : ℝ × E) :
    fderiv ℝ (fun p : ℝ × E => p.1 • p.2) z d = z.1 • d.2 + d.1 • z.2 := by
  rw [fderiv_fun_smul differentiableAt_fst differentiableAt_snd]
  rw [hasFDerivAt_fst.fderiv, hasFDerivAt_snd.fderiv]
  rfl

def radialCoframeJacobi (T : E → E →L[ℝ] E) (z : ℝ × E) : E →L[ℝ] E :=
  z.1 • (T (z.1 • z.2)).inverse

def radialCoframeJacobiVelocity (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (T : E → E →L[ℝ] E) (z : ℝ × E) : E →L[ℝ] E :=
  (T (z.1 • z.2)).inverse.comp
    (ContinuousLinearMap.id ℝ E + z.1 • Γ (z.1 • z.2) z.2)

def radialJacobiCoefficient (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (T : E → E →L[ℝ] E) (z : ℝ × E) : E →L[ℝ] E :=
  let x := z.1 • z.2
  let v := z.2
  (T x).inverse.comp
    ((((fderiv ℝ Γ x).flip v).flip v - (fderiv ℝ Γ x v).flip v +
      (Γ x).flip (Γ x v v) - (Γ x v).comp ((Γ x).flip v)).comp (T x))

@[simp] theorem radialJacobiCoefficient_apply
    (Γ : E → E →L[ℝ] E →L[ℝ] E) (T : E → E →L[ℝ] E)
    (z : ℝ × E) (w : E) :
    radialJacobiCoefficient Γ T z w = (T (z.1 • z.2)).inverse
      (christoffelCurvature Γ (z.1 • z.2) (T (z.1 • z.2) w) z.2 z.2) := rfl

variable [CompleteSpace E]

theorem contDiff_radialCoframeJacobi
    {T : E → E →L[ℝ] E} (hT : ContDiff ℝ ∞ T)
    (hTi : ∀ x, (T x).IsInvertible) : ContDiff ℝ ∞ (radialCoframeJacobi T) := by
  have hi : ContDiff ℝ ∞ (fun x => (T x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    exact fun x => (hTi x).contDiffAt_map_inverse.comp x hT.contDiffAt
  exact contDiff_fst.smul (hi.comp (contDiff_fst.smul contDiff_snd))

theorem contDiff_radialCoframeJacobiVelocity
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    {T : E → E →L[ℝ] E} (hT : ContDiff ℝ ∞ T)
    (hTi : ∀ x, (T x).IsInvertible) :
    ContDiff ℝ ∞ (radialCoframeJacobiVelocity Γ T) := by
  have hi : ContDiff ℝ ∞ (fun x => (T x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    exact fun x => (hTi x).contDiffAt_map_inverse.comp x hT.contDiffAt
  exact (hi.comp (contDiff_fst.smul contDiff_snd)).clm_comp
    (contDiff_const.add (contDiff_fst.smul
      ((hΓ.comp (contDiff_fst.smul contDiff_snd)).clm_apply contDiff_snd)))

theorem contDiff_radialJacobiCoefficient
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    {T : E → E →L[ℝ] E} (hT : ContDiff ℝ ∞ T)
    (hTi : ∀ x, (T x).IsInvertible) :
    ContDiff ℝ ∞ (radialJacobiCoefficient Γ T) := by
  have hi : ContDiff ℝ ∞ (fun x => (T x).inverse) := by
    rw [contDiff_iff_contDiffAt]
    exact fun x => (hTi x).contDiffAt_map_inverse.comp x hT.contDiffAt
  have hd : ContDiff ℝ ∞ (fderiv ℝ Γ) := hΓ.fderiv_right (by simp)
  have hf : ContDiff ℝ ∞ (fun A : E →L[ℝ] E →L[ℝ] E => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E E).contDiff
  have hf' : ContDiff ℝ ∞ (fun A : E →L[ℝ] E →L[ℝ] E →L[ℝ] E => A.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] E)).contDiff
  have hq : ContDiff ℝ ∞ (fun z : ℝ × E => z.1 • z.2) :=
    contDiff_fst.smul contDiff_snd
  have hgp := hΓ.comp hq
  have hdp := hd.comp hq
  exact (hi.comp hq).clm_comp
    (((((hf.comp ((hf'.comp hdp).clm_apply contDiff_snd)).clm_apply contDiff_snd).sub
      ((hf.comp (hdp.clm_apply contDiff_snd)).clm_apply contDiff_snd)).add
      ((hf.comp hgp).clm_apply ((hgp.clm_apply contDiff_snd).clm_apply contDiff_snd))).sub
      ((hgp.clm_apply contDiff_snd).clm_comp
        ((hf.comp hgp).clm_apply contDiff_snd)) |>.clm_comp (hT.comp hq))

variable [FiniteDimensional ℝ E]

theorem radialJacobiCoefficient_eq_kernel
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    (hgeo : ∀ x : E, ∀ t : ℝ, Γ (t • x) x x = 0)
    {T : E → E →L[ℝ] E} (hTv : ∀ x v, T x v = field Γ v x)
    (z : ℝ × E) (w : E) :
    radialJacobiCoefficient Γ T z w =
      radialCurvatureKernel Γ T (z.1 • z.2) w z.2 z.2 := by
  simp only [radialJacobiCoefficient_apply, radialCurvatureKernel_apply,
    radial_transport_ray_velocity hΓ hgeo hTv]

theorem radialCoframeJacobi_equations
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    (hsymm : ∀ x v w : E, Γ x v w = Γ x w v)
    (hgeo : ∀ x : E, ∀ t : ℝ, Γ (t • x) x x = 0)
    {T : E → E →L[ℝ] E} (hT : ContDiff ℝ ∞ T)
    (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field Γ v x) (z : ℝ × E) :
    Poincare.ODE.Parameter.timeFDeriv (radialCoframeJacobi T) z =
        radialCoframeJacobiVelocity Γ T z ∧
      Poincare.ODE.Parameter.timeFDeriv (radialCoframeJacobiVelocity Γ T) z =
        -(radialJacobiCoefficient Γ T z).comp (radialCoframeJacobi T z) := by
  let q : ℝ × E → E := fun p => p.1 • p.2
  let S : ℝ × E → E →L[ℝ] E := fun p => T (q p)
  have hq : ContDiff ℝ ∞ q := contDiff_fst.smul contDiff_snd
  have hS : ContDiff ℝ ∞ S := hT.comp hq
  have hpar : fderiv ℝ S z (1, 0) =
      -(Γ (q z) (fderiv ℝ q z (1, 0))).comp (S z) := by
    rw [show S = T ∘ q from rfl,
      fderiv_comp z ((hT.differentiable (by simp)).differentiableAt)
        ((hq.differentiable (by simp)).differentiableAt)]
    simp only [ContinuousLinearMap.comp_apply, q, fderiv_time_radial_parameter,
      smul_zero, one_smul, zero_add]
    exact fderiv_radial_transport hΓ hT hTv z.2 z.1
  have hvel : (fun p => fderiv ℝ q p (1, 0)) = fun p => p.2 := by
    funext p
    simp only [q, fderiv_time_radial_parameter, smul_zero, one_smul, zero_add]
  have hacc (p : ℝ × E) :
      covDerivAlong Γ q (fun r => fderiv ℝ q r (1, 0)) (1, 0) p = 0 := by
    rw [hvel, covDerivAlong, hasFDerivAt_snd.fderiv]
    simp only [q, fderiv_time_radial_parameter, smul_zero, one_smul, zero_add,
      hgeo]
    exact zero_add (0 : E)
  have hJ := contDiff_radialCoframeJacobi hT hTi
  have hV := contDiff_radialCoframeJacobiVelocity hΓ hT hTi
  have happly {F : ℝ × E → E →L[ℝ] E} (hF : ContDiff ℝ ∞ F) (w : E) :
      fderiv ℝ (fun p => F p w) z (1, 0) =
        Poincare.ODE.Parameter.timeFDeriv F z w := by
    rw [((hF.differentiable (by simp)).differentiableAt.hasFDerivAt.clm_apply
      (hasFDerivAt_const w z)).fderiv]
    simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
    rfl
  have hjac (w : E) :
      covDerivAlong Γ q (covDerivAlong Γ q (fun p => p.1 • w) (1, 0)) (1, 0) z =
        -christoffelCurvature Γ (q z) (z.1 • w) z.2 z.2 := by
    have he : (fun p => fderiv ℝ q p (0, w)) = fun p => p.1 • w := by
      funext p
      simp only [q, fderiv_time_radial_parameter, zero_smul, add_zero]
    have h := covDerivAlong_geodesic_family_jacobi
      (hq.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))
      ((hΓ.differentiable (by simp)).differentiableAt)
      (Filter.Eventually.of_forall fun p => hsymm (q p))
      (Filter.Eventually.of_forall hacc) (ds := (0, w)) (p := z)
    rw [he] at h
    simp only [q, fderiv_time_radial_parameter, smul_zero, zero_smul,
      one_smul, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left h
  have hDV (w : E) : covDerivAlong Γ q (fun p => p.1 • w) (1, 0) =
      fun p => w + Γ (q p) p.2 (p.1 • w) := by
    funext p
    rw [covDerivAlong, fderiv_fun_smul differentiableAt_fst (differentiableAt_const w)]
    simp only [fderiv_const_apply, smul_zero, zero_add, hasFDerivAt_fst.fderiv,
      q, fderiv_time_radial_parameter, one_smul]
    change (1 : ℝ) • w + _ = w + _
    rw [one_smul]
  constructor
  · ext w
    rw [← happly hJ w]
    have he : (fun p => radialCoframeJacobi T p w) =
        fun p => (S p).inverse (p.1 • w) := by
      funext p
      simp only [radialCoframeJacobi, smul_apply, map_smul, S, q]
    have hw : ContDiff ℝ ∞ (fun p : ℝ × E => p.1 • w) :=
      contDiff_fst.smul contDiff_const
    rw [he, fderiv_inverse_transport_apply (V := fun p => p.1 • w)
      ((hw.differentiable (by simp)).differentiableAt)
      ((hS.differentiable (by simp)).differentiableAt) (hTi (q z)) hpar, hDV]
    simp only [radialCoframeJacobiVelocity, ContinuousLinearMap.comp_apply,
      add_apply, ContinuousLinearMap.id_apply, smul_apply,
      map_smul, S, q]
  · ext w
    rw [← happly hV w]
    have he : (fun p => radialCoframeJacobiVelocity Γ T p w) =
        fun p => (S p).inverse (covDerivAlong Γ q (fun r => r.1 • w) (1, 0) p) := by
      rw [hDV]
      funext p
      simp only [radialCoframeJacobiVelocity, ContinuousLinearMap.comp_apply,
        add_apply, ContinuousLinearMap.id_apply, smul_apply,
        map_smul, S, q]
    have hw : ContDiff ℝ ∞ (fun p : ℝ × E => p.1 • w) :=
      contDiff_fst.smul contDiff_const
    rw [he, fderiv_inverse_transport_apply
      (V := covDerivAlong Γ q (fun r => r.1 • w) (1, 0))
      ((contDiffAt_covDerivAlong hΓ.contDiffAt hq.contDiffAt
        hw.contDiffAt (1, 0)).differentiableAt (by simp))
      ((hS.differentiable (by simp)).differentiableAt) (hTi (q z)) hpar, hjac]
    simp only [neg_apply, ContinuousLinearMap.comp_apply, radialJacobiCoefficient_apply,
      radialCoframeJacobi, smul_apply, ← map_smul,
      (hTi (q z)).self_apply_inverse, map_neg, S, q]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem radialCoframeJacobi_zero
    (T : E → E →L[ℝ] E) (x : E) : radialCoframeJacobi T (0, x) = 0 := by
  simp [radialCoframeJacobi]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
@[simp] theorem radialCoframeJacobi_one
    (T : E → E →L[ℝ] E) (x : E) :
    radialCoframeJacobi T (1, x) = (T x).inverse := by
  simp [radialCoframeJacobi]

omit [FiniteDimensional ℝ E] in
theorem radialCoframeJacobiVelocity_zero
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    {T : E → E →L[ℝ] E} (hTv : ∀ x v, T x v = field Γ v x) (x : E) :
    radialCoframeJacobiVelocity Γ T (0, x) = ContinuousLinearMap.id ℝ E := by
  have hT0 : T 0 = ContinuousLinearMap.id ℝ E := by
    ext v
    simpa only [ContinuousLinearMap.id_apply, field_zero hΓ] using hTv 0 v
  simp [radialCoframeJacobiVelocity, hT0]

theorem norm_iteratedFDeriv_radial_coframe_le
    {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiff ℝ ∞ Γ)
    (hsymm : ∀ x v w : E, Γ x v w = Γ x w v)
    (hgeo : ∀ x : E, ∀ t : ℝ, Γ (t • x) x x = 0)
    {T : E → E →L[ℝ] E} (hT : ContDiff ℝ ∞ T)
    (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field Γ v x)
    {U : Set E} (hU : IsOpen U) (m : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ j ≤ m, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ U,
      ‖iteratedFDeriv ℝ j (fun y => radialJacobiCoefficient Γ T (t, y)) x‖ ≤ C)
    {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ m (fun y => (T y).inverse) x‖ ≤
      Real.exp ((2 : ℝ) ^ m * max 1 C) := by
  have hJ := contDiff_radialCoframeJacobi hT hTi
  have hV := contDiff_radialCoframeJacobiVelocity hΓ hT hTi
  have hb := Poincare.ODE.Jacobi.norm_iteratedFDeriv_matrixJacobi_le
    m (a := 0) (b := 1) zero_le_one hC hU isOpen_univ (subset_univ _)
    (contDiff_radialJacobiCoefficient hΓ hT hTi).contDiffOn hJ.contDiffOn hV.contDiffOn
    (fun z _ => (radialCoframeJacobi_equations hΓ hsymm hgeo hT hTi hTv z).1)
    (fun z _ => (radialCoframeJacobi_equations hΓ hsymm hgeo hT hTi hTv z).2)
    (fun y _ => radialCoframeJacobi_zero T y)
    (fun y _ => radialCoframeJacobiVelocity_zero hΓ hTv y) hbound
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩) hx
  let π : ((E →L[ℝ] E) × (E →L[ℝ] E)) →L[ℝ] (E →L[ℝ] E) :=
    ContinuousLinearMap.fst ℝ _ _
  have hpair : ContDiff ℝ ∞ (fun y =>
      (radialCoframeJacobi T (1, y), radialCoframeJacobiVelocity Γ T (1, y))) :=
    (hJ.comp (contDiff_const.prodMk contDiff_id)).prodMk
      (hV.comp (contDiff_const.prodMk contDiff_id))
  have hproj := π.norm_iteratedFDeriv_comp_left (x := x) hpair.contDiffAt
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)
  have hπ : ‖π‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun p => by change ‖p.1‖ ≤ 1 * ‖p‖; simpa only [one_mul] using norm_fst_le p)
  have hh := hproj.trans (mul_le_mul_of_nonneg_right hπ (norm_nonneg _))
  change ‖iteratedFDeriv ℝ m (fun y => radialCoframeJacobi T (1, y)) x‖ ≤
    1 * ‖iteratedFDeriv ℝ m (fun y =>
      (radialCoframeJacobi T (1, y), radialCoframeJacobiVelocity Γ T (1, y))) x‖ at hh
  rw [one_mul] at hh
  simpa only [radialCoframeJacobi_one, sub_zero, mul_one] using hh.trans hb

end PoincareConjecture.CoordinateExponential
