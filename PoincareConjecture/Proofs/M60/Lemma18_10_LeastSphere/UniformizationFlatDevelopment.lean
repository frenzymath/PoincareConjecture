import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationConjugate
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.FrameChange
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.FrameCoordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.DerivativeLipschitz
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RoundLaplacian
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.ConformalLinearMap
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationIsothermal
import PoincareConjecture.Proofs.M01.ConnectionExistence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField Bundle
open ComplexConjugate
open scoped Manifold ContDiff Bundle Topology NNReal

noncomputable section

namespace PoincareConjecture.M60

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem plane_field_smooth {X : Plane → Plane} (hX : ContDiff ℝ ∞ X) :
    ContMDiff (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (fun x => (⟨x, X x⟩ : TangentBundle (𝓡 2) Plane)) := by
  intro x
  rw [contMDiffAt_totalSpace]
  exact ⟨contMDiffAt_id, by simpa using contMDiffAt_iff_contDiffAt.mpr hX.contDiffAt⟩

theorem exists_flat_connection_primitive
    (g : RiemannianMetric 2 Plane) (D : LeviCivitaData g)
    (e₁ e₂ : Plane → Plane) (he₁ : ContDiff ℝ ∞ e₁) (he₂ : ContDiff ℝ ∞ e₂)
    (hu₁ : ∀ x, g.inner x (e₁ x) (e₁ x) = 1)
    (hu₂ : ∀ x, g.inner x (e₂ x) (e₂ x) = 1)
    (ho : ∀ x, g.inner x (e₁ x) (e₂ x) = 0)
    (hflat : ∀ x, D.scalarCurvature x = 0) :
    ∃ theta : Plane → ℝ, ContDiff ℝ ∞ theta ∧
      ∀ x v, fderiv ℝ theta x v = g.inner x (D.connection e₁ x v) (e₂ x) := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let X : Plane → Plane := fun _ => b 0
  let Y : Plane → Plane := fun _ => b 1
  let A := D.surfaceConnectionForm e₁ e₂ X
  let B := D.surfaceConnectionForm e₁ e₂ Y
  have h₁ := plane_field_smooth he₁
  have h₂ := plane_field_smooth he₂
  have hX : ContMDiff (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (fun x => (⟨x, X x⟩ : TangentBundle (𝓡 2) Plane)) :=
    plane_field_smooth contDiff_const
  have hY : ContMDiff (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞
      (fun x => (⟨x, Y x⟩ : TangentBundle (𝓡 2) Plane)) :=
    plane_field_smooth contDiff_const
  have hA : ContDiff ℝ ∞ A := contDiff_iff_contDiffAt.mpr fun x =>
    contMDiffAt_iff_contDiffAt.mp
      (D.contMDiffAt_inner_covariantDerivativeOnFields (hX x) (h₁ x) (h₂ x))
  have hB : ContDiff ℝ ∞ B := contDiff_iff_contDiffAt.mpr fun x =>
    contMDiffAt_iff_contDiffAt.mp
      (D.contMDiffAt_inner_covariantDerivativeOnFields (hY x) (h₁ x) (h₂ x))
  have hbracket : mlieBracket (𝓡 2) X Y = 0 := by
    funext x
    simp only [X, Y, mlieBracket, mlieBracketWithin_eq_lieBracketWithin,
      lieBracketWithin, fderivWithin_univ, fderiv_const_apply]
    simp +instances
  have hcurl (x : Plane) : fderiv ℝ B x (b 0) - fderiv ℝ A x (b 1) = 0 := by
    have h := D.curvatureTensor_eq_exteriorDerivative_surfaceConnectionForm
      isOpen_univ (mem_univ x) h₁.contMDiffOn h₂.contMDiffOn
      (fun y _ => hu₁ y) (fun y _ => hu₂ y) (fun y _ => ho y) (hX x) (hY x)
    rw [D.curvatureTensor_eq_half_scalarCurvature, hflat x] at h
    simp only [hbracket, LeviCivitaData.surfaceConnectionForm,
      LeviCivitaData.covariantDerivativeOnFields, Pi.zero_apply,
      map_zero] at h
    simpa [A, B, X, Y, mvfderiv, mfderiv_eq_fderiv,
      LeviCivitaData.surfaceConnectionForm, LeviCivitaData.covariantDerivativeOnFields]
      using! h.symm
  obtain ⟨theta, htheta, hd⟩ := exists_conjugate_of_divergence_zero hB hA.neg
    (show StarConvex ℝ (0 : Plane) univ from convex_univ.starConvex (mem_univ _))
    (fun x _ => by
      rw [show (fun y => -A y) = -A from rfl, fderiv_neg]
      exact hcurl x)
  refine ⟨theta, htheta, fun x v => ?_⟩
  rw [(hd x (mem_univ x)).fderiv]
  let L : Plane →L[ℝ] ℝ := ((g.euclideanCoefficients x).flip (e₂ x)).comp (D.connection e₁ x)
  have hL := plane_form_apply L v
  simpa only [rotatedFlux, A, B, X, Y, L, b, Pi.neg_apply, neg_neg,
    add_apply, smul_apply, smul_eq_mul, EuclideanSpace.coe_proj,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    RiemannianMetric.euclideanCoefficients, LeviCivitaData.surfaceConnectionForm,
    LeviCivitaData.covariantDerivativeOnFields] using! hL.symm

theorem exists_parallel_frame_of_flat_plane
    (g : RiemannianMetric 2 Plane) (D : LeviCivitaData g)
    (hflat : ∀ x, D.scalarCurvature x = 0) :
    ∃ e₁ e₂ : Plane → Plane, ContDiff ℝ ∞ e₁ ∧ ContDiff ℝ ∞ e₂ ∧
      (∀ x, g.inner x (e₁ x) (e₁ x) = 1) ∧
      (∀ x, g.inner x (e₂ x) (e₂ x) = 1) ∧
      (∀ x, g.inner x (e₁ x) (e₂ x) = 0) ∧
      (∀ x v, D.connection e₁ x v = 0) ∧
      (∀ x v, D.connection e₂ x v = 0) := by
  classical
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  obtain ⟨u₁, u₂, hu₁, hu₂, hunit₁, hunit₂, horth, _⟩ :=
    g.exists_orthonormal_frame_of_independent_fields
      (plane_field_smooth (X := fun _ => b 0) contDiff_const).contMDiffOn
      (plane_field_smooth (X := fun _ => b 1) contDiff_const).contMDiffOn
      (U := univ) (fun _ _ => by
        have hb : (![b 0, b 1] : Fin 2 → Plane) = b := by
          funext i
          fin_cases i <;> rfl
        rw [hb]
        exact b.toBasis.linearIndependent)
  have hs₁ : ContDiff ℝ ∞ u₁ := contDiff_iff_contDiffAt.mpr fun x => by
    have h := (contMDiffAt_totalSpace.mp ((contMDiffOn_univ.mp hu₁) x)).2
    exact contMDiffAt_iff_contDiffAt.mp (by simpa using h)
  have hs₂ : ContDiff ℝ ∞ u₂ := contDiff_iff_contDiffAt.mpr fun x => by
    have h := (contMDiffAt_totalSpace.mp ((contMDiffOn_univ.mp hu₂) x)).2
    exact contMDiffAt_iff_contDiffAt.mp (by simpa using h)
  have hu₁' (x) := hunit₁ x (mem_univ x)
  have hu₂' (x) := hunit₂ x (mem_univ x)
  have ho (x) := horth x (mem_univ x)
  have ho' (x) : g.inner x (u₂ x) (u₁ x) = 0 := (g.symm x _ _).trans (ho x)
  obtain ⟨theta, htheta, hdtheta⟩ :=
    exists_flat_connection_primitive g D u₁ u₂ hs₁ hs₂ hu₁' hu₂' ho hflat
  let c : Plane → ℝ := fun x => Real.cos (-theta x)
  let s : Plane → ℝ := fun x => Real.sin (-theta x)
  let e₁ : Plane → Plane := fun x => c x • u₁ x + s x • u₂ x
  let e₂ : Plane → Plane := fun x => -s x • u₁ x + c x • u₂ x
  have hc : ContDiff ℝ ∞ c := Real.contDiff_cos.comp htheta.neg
  have hs : ContDiff ℝ ∞ s := Real.contDiff_sin.comp htheta.neg
  have he₁ : ContDiff ℝ ∞ e₁ := (hc.smul hs₁).add (hs.smul hs₂)
  have he₂ : ContDiff ℝ ∞ e₂ := (hs.neg.smul hs₁).add (hc.smul hs₂)
  have hcs (x) : c x ^ 2 + s x ^ 2 = 1 := by
    simpa only [c, s, add_comm] using Real.sin_sq_add_cos_sq (-theta x)
  have heunit₁ (x) : g.inner x (e₁ x) (e₁ x) = 1 := by
    simp only [e₁, map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
      hu₁', hu₂', ho, ho', mul_zero, mul_one, add_zero, zero_add]
    nlinarith [hcs x]
  have heunit₂ (x) : g.inner x (e₂ x) (e₂ x) = 1 := by
    simp only [e₂, map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
      hu₁', hu₂', ho, ho', mul_zero, mul_one, add_zero, zero_add]
    nlinarith [hcs x]
  have heorth (x) : g.inner x (e₁ x) (e₂ x) = 0 := by
    simp only [e₁, e₂, map_add, add_apply, map_smul, smul_apply, smul_eq_mul,
      hu₁', hu₂', ho, ho', mul_zero, mul_one, add_zero, zero_add]
    ring
  have hform (x v : Plane) : g.inner x (D.connection e₁ x v) (e₂ x) = 0 := by
    have h := D.surfaceConnectionForm_rotate_angle (fun _ => v)
      ((plane_field_smooth hs₁) x) ((plane_field_smooth hs₂) x)
      (Eventually.of_forall hu₁') (Eventually.of_forall hu₂')
      (Eventually.of_forall ho)
      ((contMDiff_iff_contDiff.mpr htheta.neg).mdifferentiable (by simp) x)
    have hder : mvfderiv (𝓡 2) (fun y => -theta y) x v =
        -g.inner x (D.connection u₁ x v) (u₂ x) := by
      simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
      change fderiv ℝ (-theta) x v = _
      rw [fderiv_neg, neg_apply, hdtheta]
    change g.inner x (D.connection e₁ x v) (e₂ x) =
      g.inner x (D.connection u₁ x v) (u₂ x) +
        mvfderiv (𝓡 2) (fun y => -theta y) x v at h
    rw [hder, add_neg_cancel] at h
    exact h
  have hz₁ (x v : Plane) : D.connection e₁ x v = 0 := by
    have hself := D.inner_covariantDerivative_unit_eq_zero (fun _ => v)
      ((plane_field_smooth he₁) x) (Eventually.of_forall heunit₁)
    rw [g.symm] at hself
    change g.inner x (D.connection e₁ x v) (e₁ x) = 0 at hself
    have heq := g.eq_frameCoordinates_smul x (heunit₁ x) (heunit₂ x) (heorth x)
      (D.connection e₁ x v)
    simpa only [hself, hform, zero_smul, zero_add] using heq
  have hz₂ (x v : Plane) : D.connection e₂ x v = 0 := by
    have hself := D.inner_covariantDerivative_unit_eq_zero (fun _ => v)
      ((plane_field_smooth he₂) x) (Eventually.of_forall heunit₂)
    rw [g.symm] at hself
    change g.inner x (D.connection e₂ x v) (e₂ x) = 0 at hself
    have hcross := D.horizon_mvfderiv_inner (fun _ => v)
      (((plane_field_smooth he₁) x).mdifferentiableAt (by simp))
      (((plane_field_smooth he₂) x).mdifferentiableAt (by simp))
    rw [Poincare.mvfderiv_eq_of_eventuallyEq (Eventually.of_forall heorth),
      mvfderiv_const] at hcross
    simp only [zero_apply, LeviCivitaData.covariantDerivativeOnFields,
      hz₁, map_zero, zero_apply, zero_add] at hcross
    rw [g.symm] at hcross
    have heq := g.eq_frameCoordinates_smul x (heunit₁ x) (heunit₂ x) (heorth x)
      (D.connection e₂ x v)
    simpa only [hself, hcross.symm, zero_smul, zero_add] using heq
  exact ⟨e₁, e₂, he₁, he₂, heunit₁, heunit₂, heorth, hz₁, hz₂⟩

theorem exists_potential_of_parallel_plane_field
    (g : RiemannianMetric 2 Plane) (D : LeviCivitaData g)
    (e : Plane → Plane) (he : ContDiff ℝ ∞ e)
    (hparallel : ∀ x v, D.connection e x v = 0) :
    ∃ f : Plane → ℝ, ContDiff ℝ ∞ f ∧
      (∀ x v, fderiv ℝ f x v = g.inner x (e x) v) ∧
      (∀ x, D.gradient f x = e x) ∧ RiemannianMetric.HasZeroHessian D f := by
  let omega : Plane → Plane →L[ℝ] ℝ := fun x => g.euclideanCoefficients x (e x)
  have hg : ContDiff ℝ ∞ g.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr fun x => g.contDiffAt_euclideanCoefficients x
  have homega : ContDiff ℝ ∞ omega := hg.clm_apply he
  have hclosed (x v w : Plane) : fderiv ℝ omega x v w = fderiv ℝ omega x w v := by
    have hc (v : Plane) := plane_field_smooth (X := fun _ => v) contDiff_const
    have hder (v w : Plane) : fderiv ℝ omega x v w =
        g.inner x (e x) (D.connection (fun _ => w) x v) := by
      have h := D.horizon_mvfderiv_inner (fun _ => v)
        (((plane_field_smooth he) x).mdifferentiableAt (by simp))
        ((hc w x).mdifferentiableAt (by simp))
      simp only [LeviCivitaData.covariantDerivativeOnFields,
        hparallel, map_zero, zero_apply, zero_add] at h
      have hd := ((homega.differentiable (by simp) x).hasFDerivAt.clm_apply
        (hasFDerivAt_const w x)).fderiv
      have heq := congrArg (fun L : Plane →L[ℝ] ℝ => L v) hd
      simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply,
        map_zero, zero_add, ContinuousLinearMap.flip_apply] at heq
      change fderiv ℝ (fun y => g.inner y (e y) w) x v = fderiv ℝ omega x v w at heq
      rw [← heq]
      simpa only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace] using! h
    rw [hder, hder]
    congr 1
    have ht := D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero
      ((hc v x).mdifferentiableAt (by simp)) ((hc w x).mdifferentiableAt (by simp))
    have hb : mlieBracket (𝓡 2) (fun _ : Plane => v) (fun _ => w) x = 0 := by
      simp only [mlieBracket, mlieBracketWithin_eq_lieBracketWithin,
        lieBracketWithin, fderivWithin_univ, fderiv_const_apply]
      simp +instances
    simpa only [hb, sub_eq_zero] using ht
  let f := radialPrimitive omega
  have hf : ContDiff ℝ ∞ f := radialPrimitive_contDiff homega
  have hdf (x : Plane) : HasFDerivAt f (omega x) x :=
    hasFDerivAt_radialPrimitive homega
      (show StarConvex ℝ (0 : Plane) univ from convex_univ.starConvex (mem_univ _))
      (fun y _ => hclosed y) (mem_univ x)
  have hgrad (x : Plane) : D.gradient f x = e x := by
    apply (g.inner_isInvertible x).injective
    ext v
    rw [D.inner_gradient]
    simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    exact congrArg (fun L : Plane →L[ℝ] ℝ => L v) (hdf x).fderiv
  refine ⟨f, hf, fun x v => congrArg (fun L : Plane →L[ℝ] ℝ => L v) (hdf x).fderiv,
    hgrad, ?_⟩
  intro x v w
  rw [D.hessian_eq_inner_connection_gradient
    ((contMDiff_iff_contDiff.mpr hf) x), show D.gradient f = e from funext hgrad,
    hparallel, map_zero, zero_apply]

theorem exists_developing_map_of_flat_plane
    (g : RiemannianMetric 2 Plane) (D : LeviCivitaData g)
    (hflat : ∀ x, D.scalarCurvature x = 0) :
    ∃ F : Plane → Plane, ContDiff ℝ ∞ F ∧
      (∀ x v w, inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w) = g.inner x v w) ∧
      (∀ i : Fin 2, RiemannianMetric.HasZeroHessian D (fun x => F x i)) := by
  obtain ⟨e₁, e₂, he₁, he₂, hu₁, hu₂, ho, hp₁, hp₂⟩ :=
    exists_parallel_frame_of_flat_plane g D hflat
  obtain ⟨f₁, hf₁, hd₁, _, hh₁⟩ := exists_potential_of_parallel_plane_field g D e₁ he₁ hp₁
  obtain ⟨f₂, hf₂, hd₂, _, hh₂⟩ := exists_potential_of_parallel_plane_field g D e₂ he₂ hp₂
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  let F : Plane → Plane := fun x => f₁ x • b 0 + f₂ x • b 1
  have hF : ContDiff ℝ ∞ F := (hf₁.smul contDiff_const).add (hf₂.smul contDiff_const)
  have hdF (x v : Plane) : fderiv ℝ F x v =
      g.inner x (e₁ x) v • b 0 + g.inner x (e₂ x) v • b 1 := by
    have h : HasFDerivAt F
        ((fderiv ℝ f₁ x).smulRight (b 0) + (fderiv ℝ f₂ x).smulRight (b 1)) x :=
      ((hf₁.differentiable (by simp) x).hasFDerivAt.smul_const (b 0)).add
        ((hf₂.differentiable (by simp) x).hasFDerivAt.smul_const (b 1))
    rw [h.fderiv]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply, hd₁, hd₂]
  have hcoord (x : Plane) : F x 0 = f₁ x ∧ F x 1 = f₂ x := by
    simp [F, b, EuclideanSpace.basisFun_apply]
  refine ⟨F, hF, fun x v w => ?_, fun i => ?_⟩
  · rw [hdF, hdF, g.inner_eq_frameCoordinates x (hu₁ x) (hu₂ x) (ho x) v w]
    have hb (i j : Fin 2) : inner ℝ (b i) (b j) = if i = j then 1 else 0 :=
      b.inner_eq_ite i j
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hb]
    norm_num
    rw [g.symm x (e₁ x) v, g.symm x (e₂ x) v,
      g.symm x (e₁ x) w, g.symm x (e₂ x) w]
    ring
  · fin_cases i
    · convert! hh₁ using 1
      exact funext fun x => (hcoord x).1
    · convert! hh₂ using 1
      exact funext fun x => (hcoord x).2

private theorem zero_hessian_geodesic_affine
    {g : RiemannianMetric 2 Plane} {D : LeviCivitaData g}
    {f : Plane → ℝ} {gamma : ℝ → Plane} {S : Set ℝ}
    (hf : ContDiff ℝ ∞ f) (hh : RiemannianMetric.HasZeroHessian D f)
    (hS : IsOpen S) (hSc : Convex ℝ S) (h0 : 0 ∈ S)
    (hgamma : g.IsGeodesicOn gamma S) {t : ℝ} (ht : t ∈ S) :
    f (gamma t) = f (gamma 0) + t * deriv (f ∘ gamma) 0 := by
  have hd (u : ℝ) (hu : u ∈ S) :=
    RiemannianMetric.hasDerivAt_deriv_comp_geodesic_eq_zero
      (contMDiff_iff_contDiff.mpr hf) hh hgamma hu
  have hconst (u : ℝ) (hu : u ∈ S) :
      deriv (f ∘ gamma) u = deriv (f ∘ gamma) 0 :=
    hS.is_const_of_deriv_eq_zero hSc.isPreconnected
      (fun v hv => (hd v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hd v hv).deriv) hu h0
  have hdiff : DifferentiableOn ℝ (f ∘ gamma) S := by
    intro u hu
    apply DifferentiableAt.differentiableWithinAt
    exact (hf.differentiable (by simp) (gamma u)).comp u
      ((contMDiffAt_iff_contDiffAt.mp (hgamma.contMDiffAt hu)).differentiableAt (by simp))
  have hlin (u : ℝ) : HasDerivAt (fun s => f (gamma 0) + s * deriv (f ∘ gamma) 0)
      (deriv (f ∘ gamma) 0) u := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id u).mul_const (deriv (f ∘ gamma) 0)).const_add (f (gamma 0))
  exact hS.eqOn_of_deriv_eq hSc.isPreconnected hdiff
    (fun u _ => (hlin u).differentiableAt.differentiableWithinAt)
    (fun u hu => (hconst u hu).trans (hlin u).deriv.symm) h0 (by simp) ht

theorem exists_diffeomorph_of_complete_flat_plane
    (g : RiemannianMetric 2 Plane) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hflat : ∀ x, D.scalarCurvature x = 0) :
    ∃ F : Plane ≃ₘ[ℝ] Plane,
      ∀ x v w, inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w) = g.inner x v w := by
  classical
  obtain ⟨F, hF, hmetric, hzero⟩ := exists_developing_map_of_flat_plane g D hflat
  have hinj (x : Plane) : Function.Injective (fderiv ℝ F x) := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    change fderiv ℝ F x v = 0 at hv
    have heq := hmetric x v v
    rw [hv, inner_zero_left] at heq
    by_contra hne
    exact (g.pos x v hne).ne' heq.symm
  let L (x : Plane) : Plane ≃L[ℝ] Plane :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ F x).toLinearMap (hinj x)).toContinuousLinearEquiv
  have hL (x : Plane) : (L x : Plane →L[ℝ] Plane) = fderiv ℝ F x := rfl
  have hfi (i : Fin 2) : ContDiff ℝ ∞ (fun x => F x i) :=
    (show Plane →L[ℝ] ℝ from EuclideanSpace.proj i).contDiff.comp hF
  have hcomp (gamma : ℝ → Plane) {S : Set ℝ} (hg : g.IsGeodesicOn gamma S)
      {t : ℝ} (ht : t ∈ S) (i : Fin 2) :
      deriv ((fun x => F x i) ∘ gamma) t = fderiv ℝ F (gamma t) (deriv gamma t) i := by
    have hdg := ((contMDiffAt_iff_contDiffAt.mp (hg.contMDiffAt ht)).differentiableAt
      (by simp)).hasDerivAt
    have h := ((EuclideanSpace.proj i).hasFDerivAt.comp (gamma t)
      (hF.differentiable (by simp) (gamma t)).hasFDerivAt).comp_hasDerivAt t hdg
    exact h.deriv
  have hsurj : Function.Surjective F := by
    intro y
    let v := (L 0).symm (y - F 0)
    obtain ⟨gamma, hg, h0, hd0⟩ := g.exists_global_geodesic hc 0 v
    have hd0' : HasDerivAt gamma v 0 := by simpa using hd0
    refine ⟨gamma 1, ?_⟩
    ext i
    have ha := zero_hessian_geodesic_affine (hfi i) (hzero i) isOpen_univ
      convex_univ (mem_univ 0) hg (mem_univ 1)
    rw [hcomp gamma hg (mem_univ 0), hd0'.deriv, h0] at ha
    have hv : fderiv ℝ F 0 v = y - F 0 := by
      rw [← hL]
      exact (L 0).apply_symm_apply (y - F 0)
    simpa only [one_mul, hv, PiLp.sub_apply, add_sub_cancel] using ha
  have hFinj : Function.Injective F := by
    intro x y hxy
    obtain ⟨epsilon, heps, gamma, hg, h0, h1, _⟩ :=
      g.exists_minimizing_geodesic_of_metricComplete hc x y
    let S := Ioo (-epsilon) (1 + epsilon)
    have hS0 : (0 : ℝ) ∈ S := ⟨by linarith, by linarith⟩
    have hS1 : (1 : ℝ) ∈ S := ⟨by linarith, by linarith⟩
    have hfirst (i : Fin 2) : deriv ((fun z => F z i) ∘ gamma) 0 = 0 := by
      have ha := zero_hessian_geodesic_affine (hfi i) (hzero i) isOpen_Ioo
        (convex_Ioo _ _) hS0 hg hS1
      rw [h0, h1, one_mul, hxy] at ha
      linarith
    have hdF (t : ℝ) (ht : t ∈ S) : fderiv ℝ F (gamma t) (deriv gamma t) = 0 := by
      ext i
      rw [← hcomp gamma hg ht i]
      have hd (u : ℝ) (hu : u ∈ S) :=
        RiemannianMetric.hasDerivAt_deriv_comp_geodesic_eq_zero
          (contMDiff_iff_contDiff.mpr (hfi i)) (hzero i) hg hu
      have heq := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo _ _).isPreconnected
        (fun u hu => (hd u hu).differentiableAt.differentiableWithinAt)
        (fun u hu => (hd u hu).deriv) ht hS0
      exact heq.trans (hfirst i)
    have hdg (t : ℝ) (ht : t ∈ S) : deriv gamma t = 0 :=
      hinj (gamma t) (by simpa only [map_zero] using hdF t ht)
    have heq := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo _ _).isPreconnected
      (fun t ht => ((contMDiffAt_iff_contDiffAt.mp (hg.contMDiffAt ht)).differentiableAt
        (by simp)).differentiableWithinAt) hdg hS0 hS1
    simpa only [h0, h1] using heq
  let e := Equiv.ofBijective F ⟨hFinj, hsurj⟩
  have hinv : ContDiff ℝ ∞ e.symm := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    let x := e.symm y
    have hFx : F x = y := e.apply_symm_apply y
    have hd : HasFDerivAt F (L x : Plane →L[ℝ] Plane) x := by
      rw [hL]
      exact (hF.differentiable (by simp) x).hasFDerivAt
    let a := hF.contDiffAt.toOpenPartialHomeomorph F hd (by simp)
    have hy : y ∈ a.target := by
      rw [← hFx]
      exact hF.contDiffAt.image_mem_toOpenPartialHomeomorph_target hd (by simp)
    have heq : e.symm =ᶠ[𝓝 y] a.symm := by
      filter_upwards [a.open_target.mem_nhds hy] with z hz
      apply hFinj
      exact (e.apply_symm_apply z).trans (a.right_inv hz).symm
    apply (a.contDiffAt_symm (f₀' := L x) hy ?_ ?_).congr_of_eventuallyEq heq
    · have hx : a.symm y = x := by
        apply hFinj
        exact (a.right_inv hy).trans hFx.symm
      simpa only [hx] using! hd
    · exact hF.contDiffAt
  let phi : Plane ≃ₘ[ℝ] Plane :=
    ⟨e, contMDiff_iff_contDiff.mpr hF, contMDiff_iff_contDiff.mpr hinv⟩
  exact ⟨phi, hmetric⟩

attribute [-instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
end PoincareConjecture.M60

end
