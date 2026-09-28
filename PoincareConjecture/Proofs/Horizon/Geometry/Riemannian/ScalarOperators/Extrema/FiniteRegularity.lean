import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Filter Set

noncomputable section

namespace PoincareConjecture.LeviCivitaData

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option backward.isDefEq.respectTransparency false in
private theorem eventually_hasDerivAt_comp_C2
    {X : (x : M) → TangentSpace (𝓡 n) x} {γ : ℝ → M} {t₀ : ℝ}
    (hγ : IsMIntegralCurveAt γ X t₀) {F : M → ℝ}
    (hF : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 F (γ t₀)) :
    ∀ᶠ t in 𝓝 t₀, HasDerivAt (F ∘ γ)
      (mvfderiv (𝓡 n) F (γ t) (X (γ t))) t := by
  have hFev : ∀ᶠ t in 𝓝 t₀, ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 F (γ t) :=
    hγ.hasMFDerivAt.continuousAt.eventually
      ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hF)
  filter_upwards [hγ, hFev] with t ht hFt
  have hFd : HasMFDerivAt (𝓡 n) 𝓘(ℝ, ℝ) F (γ t)
      (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) F (γ t)) :=
    (hFt.mdifferentiableAt (by simp)).hasMFDerivAt
  have hcomp := hFd.comp t ht
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply hcomp.congr_mfderiv
  ext
  exact (congrArg (mfderiv (𝓡 n) 𝓘(ℝ, ℝ) F (γ t))
    (one_smul ℝ (X (γ t)))).trans (one_smul ℝ _).symm

private theorem exists_integralCurve_extend (q : M)
    (v : TangentSpace (𝓡 n) q) :
    ∃ γ : ℝ → M, γ 0 = q ∧
      IsMIntegralCurveAt γ (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) 0 := by
  apply exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless 0
  exact FiberBundle.contMDiffAt_extend (k := 1) (𝓡 n)
    (EuclideanSpace ℝ (Fin n)) v

theorem mvfderiv_eq_zero_of_isLocalMax_contMDiffAt
    {f : M → ℝ} {q : M} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f q)
    (hmax : IsLocalMax f q) : mvfderiv (𝓡 n) f q = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨γ, hγ0, hγ⟩ := exists_integralCurve_extend q v
  have hfγ : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f (γ 0) := hγ0.symm ▸ hf
  have h0 := (eventually_hasDerivAt_comp_C2 hγ hfγ).self_of_nhds
  have hcont : ContinuousAt γ 0 := hγ.hasMFDerivAt.continuousAt
  have hmax' : IsLocalMax (f ∘ γ) 0 := by
    have htend : Tendsto γ (𝓝 0) (𝓝 q) := hγ0 ▸ hcont.tendsto
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), f (γ t) ≤ f q := htend.eventually hmax
    filter_upwards [hev] with t ht
    simpa [Function.comp, hγ0] using ht
  have hz : deriv (f ∘ γ) 0 = 0 := hmax'.deriv_eq_zero
  rw [h0.deriv, hγ0, FiberBundle.extend_apply_self] at hz
  exact hz

private theorem contMDiffAt_mvfderiv_apply_C2
    {f : M → ℝ} {q : M} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f q)
    {X : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      1 (T% X) q) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 1
      (fun y => mvfderiv (𝓡 n) f y (X y)) q := by
  have hdf : ContMDiffAt (𝓡 n) ((𝓡 n).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) 1
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) y
        (mvfderiv (𝓡 n) f y)) q := by
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    convert hf.mfderiv_const (m := 1) (by norm_num) using 1
    funext y
    simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates, mvfderiv,
      NormedSpace.fromTangentSpace]
    rfl
  have h := hdf.clm_bundle_apply hX
  simpa using (Bundle.contMDiffAt_totalSpace.mp h).2

theorem hessian_nonpos_of_isLocalMax_contMDiffAt
    (D : LeviCivitaData g) {f : M → ℝ} {q : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f q)
    (hmax : IsLocalMax f q) (v : TangentSpace (𝓡 n) q) :
    D.hessian f q v v ≤ 0 := by
  have hcrit : mvfderiv (𝓡 n) f q = 0 :=
    mvfderiv_eq_zero_of_isLocalMax_contMDiffAt hf hmax
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  obtain ⟨γ, hγ0, hγ⟩ := exists_integralCurve_extend q v
  have hfγ : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f (γ 0) := hγ0.symm ▸ hf
  have hφev : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (f ∘ γ)
      (mvfderiv (𝓡 n) f (γ t) (X (γ t))) t :=
    eventually_hasDerivAt_comp_C2 hγ hfγ
  have hφ' : deriv (f ∘ γ) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => mvfderiv (𝓡 n) f (γ t) (X (γ t))) := by
    filter_upwards [hφev] with t ht
    exact ht.deriv
  have hXf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 1
      (fun y => mvfderiv (𝓡 n) f y (X y)) q :=
    contMDiffAt_mvfderiv_apply_C2 hf
      (FiberBundle.contMDiffAt_extend (k := 1)
        (𝓡 n) (EuclideanSpace ℝ (Fin n)) v)
  have h2 : HasDerivAt
      (fun t => mvfderiv (𝓡 n) f (γ t) (X (γ t)))
      (mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y (X y))
        (γ 0) (X (γ 0))) 0 := by
    have hFd0 := (hXf.mdifferentiableAt (by simp)).hasMFDerivAt
    rw [← hγ0] at hFd0
    have hcomp := hFd0.comp 0 hγ.hasMFDerivAt
    rw [hasDerivAt_iff_hasFDerivAt]
    apply hcomp.hasFDerivAt.congr_fderiv
    ext
    exact (congrArg (mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => mvfderiv (𝓡 n) f y (X y)) (γ 0))
      (one_smul ℝ (X (γ 0)))).trans (one_smul ℝ _).symm
  have hdd : deriv (deriv (f ∘ γ)) 0 =
      mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y (X y)) q (X q) := by
    rw [Filter.EventuallyEq.deriv_eq hφ', h2.deriv, hγ0]
  have hcont : ContinuousAt γ 0 := hγ.hasMFDerivAt.continuousAt
  have hmax' : IsLocalMax (f ∘ γ) 0 := by
    have htend : Tendsto γ (𝓝 0) (𝓝 q) := hγ0 ▸ hcont.tendsto
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), f (γ t) ≤ f q := htend.eventually hmax
    filter_upwards [hev] with t ht
    simpa [Function.comp, hγ0] using ht
  have hφcont : ContinuousAt (f ∘ γ) 0 := hfγ.continuousAt.comp hcont
  have hnonpos := deriv_deriv_nonpos_of_isLocalMax hmax' hφcont
  have hconn : mvfderiv (𝓡 n) f q
      (D.connection X q (X q)) = 0 := by simp [hcrit]
  unfold hessian hessianOnFields
  change mvfderiv (𝓡 n) (fun y => mvfderiv (𝓡 n) f y (X y)) q (X q) -
      mvfderiv (𝓡 n) f q (D.connection X q (X q)) ≤ 0
  rw [← hdd, hconn, sub_zero]
  exact hnonpos

theorem hessian_nonneg_of_isLocalMin_contMDiffAt
    (D : LeviCivitaData g) {f : M → ℝ} {q : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f q)
    (hmin : IsLocalMin f q) (v : TangentSpace (𝓡 n) q) :
    0 ≤ D.hessian f q v v := by
  have h := hessian_nonpos_of_isLocalMax_contMDiffAt D (f := fun x => -f x)
    hf.neg (q := q) hmin.neg v
  have hneg : D.hessian (fun x => -f x) q v v = -D.hessian f q v v := by
    unfold hessian hessianOnFields
    have hfun : (fun z => -f z) = -f := rfl
    rw [hfun]
    simp only [mvfderiv_neg, neg_apply]
    change mvfderiv (𝓡 n)
      (-(fun x => mvfderiv (𝓡 n) f x
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v x))) q
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v q) - _ = _
    rw [mvfderiv_neg, neg_apply]
    ring
  rw [hneg] at h
  linarith

theorem laplacian_nonpos_of_isLocalMax_contMDiffAt
    (D : LeviCivitaData g) {f : M → ℝ} {q : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f q)
    (hmax : IsLocalMax f q) : D.laplacian f q ≤ 0 := by
  unfold laplacian
  exact Finset.sum_nonpos fun i _ => D.hessian_nonpos_of_isLocalMax_contMDiffAt hf hmax _

theorem laplacian_nonneg_of_isLocalMin_contMDiffAt
    (D : LeviCivitaData g) {f : M → ℝ} {q : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) 2 f q)
    (hmin : IsLocalMin f q) : 0 ≤ D.laplacian f q := by
  unfold laplacian
  exact Finset.sum_nonneg fun i _ => D.hessian_nonneg_of_isLocalMin_contMDiffAt hf hmin _

theorem mvfderiv_eq_zero_of_isLocalMax_C2
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 2 f) {q : M}
    (hmax : IsLocalMax f q) : mvfderiv (𝓡 n) f q = 0 :=
  mvfderiv_eq_zero_of_isLocalMax_contMDiffAt (hf q) hmax

theorem hessian_nonpos_of_isLocalMax_C2
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 2 f) {q : M}
    (hmax : IsLocalMax f q) (v : TangentSpace (𝓡 n) q) :
    D.hessian f q v v ≤ 0 :=
  D.hessian_nonpos_of_isLocalMax_contMDiffAt (hf q) hmax v

theorem hessian_nonneg_of_isLocalMin_C2
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 2 f) {q : M}
    (hmin : IsLocalMin f q) (v : TangentSpace (𝓡 n) q) :
    0 ≤ D.hessian f q v v :=
  D.hessian_nonneg_of_isLocalMin_contMDiffAt (hf q) hmin v

theorem laplacian_nonpos_of_isLocalMax_C2
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 2 f) {q : M}
    (hmax : IsLocalMax f q) : D.laplacian f q ≤ 0 :=
  D.laplacian_nonpos_of_isLocalMax_contMDiffAt (hf q) hmax

theorem laplacian_nonneg_of_isLocalMin_C2
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 2 f) {q : M}
    (hmin : IsLocalMin f q) : 0 ≤ D.laplacian f q :=
  D.laplacian_nonneg_of_isLocalMin_contMDiffAt (hf q) hmin

end PoincareConjecture.LeviCivitaData
