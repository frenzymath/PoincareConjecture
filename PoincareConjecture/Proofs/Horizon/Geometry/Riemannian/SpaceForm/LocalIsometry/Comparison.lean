import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.ExponentialMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.LocalInverse
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.SpaceForm

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem bijective_mfderiv_of_spherical_metric
    (g : RiemannianMetric n M) {e : EuclideanSpace ℝ (Fin n) → M}
    (hzero : ∀ u v, g.pullbackCoefficients e 0 u v = inner ℝ u v)
    (hpolar : ∀ (θ w z : EuclideanSpace ℝ (Fin n)), inner ℝ θ θ = 1 →
      ∀ t : ℝ, 0 ≤ t → t < 1 →
        t ^ 2 * g.pullbackCoefficients e (t • θ) w z =
          Real.sin t ^ 2 * inner ℝ w z +
            (t ^ 2 - Real.sin t ^ 2) * inner ℝ w θ * inner ℝ z θ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball 0 1) :
    Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e x) := by
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) e x
  have hinj : Function.Injective A := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    have hz : g.pullbackCoefficients e x w w = 0 := by
      change mfderiv (𝓡 n) (𝓡 n) e x w = 0 at hw
      change g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x w)
        (mfderiv (𝓡 n) (𝓡 n) e x w) = 0
      rw [hw]
      simp
    by_cases hx0 : x = 0
    · rw [hx0, hzero] at hz
      exact inner_self_eq_zero.mp hz
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hr1 : ‖x‖ < 1 := by simpa using hx
    let θ : EuclideanSpace ℝ (Fin n) := ‖x‖⁻¹ • x
    have hθ : inner ℝ θ θ = 1 := by
      simp [θ, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), ne_of_gt hr]
    have hθx : ‖x‖ • θ = x := by simp [θ, smul_smul, ne_of_gt hr]
    have hs : 0 < Real.sin ‖x‖ :=
      Real.sin_pos_of_pos_of_lt_pi hr (hr1.trans (by linarith [Real.pi_gt_three]))
    have hsle := Real.sin_le hr.le
    have hcoeff : 0 ≤ ‖x‖ ^ 2 - Real.sin ‖x‖ ^ 2 := by nlinarith
    have hnonneg : 0 ≤ (‖x‖ ^ 2 - Real.sin ‖x‖ ^ 2) * inner ℝ w θ ^ 2 :=
      mul_nonneg hcoeff (sq_nonneg _)
    have h := hpolar θ w w hθ ‖x‖ hr.le hr1
    rw [hθx, hz, mul_zero] at h
    have hi : inner ℝ w w = 0 := by
      have hipos : 0 ≤ inner ℝ w w := real_inner_self_nonneg
      have hsin2 : 0 < Real.sin ‖x‖ ^ 2 := sq_pos_of_pos hs
      nlinarith
    exact inner_self_eq_zero.mp hi
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hinj⟩

theorem exists_local_isometry_of_spherical_exponentials
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    {p : M} {q : N} {e : EuclideanSpace ℝ (Fin n) → M}
    {f : EuclideanSpace ℝ (Fin n) → N}
    (he0 : e 0 = p) (hf0 : f 0 = q)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 1))
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 1))
    (hemetric : ∀ u v, g.pullbackCoefficients e 0 u v = inner ℝ u v)
    (hfmetric : ∀ u v, h.pullbackCoefficients f 0 u v = inner ℝ u v)
    (hepolar : ∀ (θ w z : EuclideanSpace ℝ (Fin n)), inner ℝ θ θ = 1 →
      ∀ t : ℝ, 0 ≤ t → t < 1 →
        t ^ 2 * g.pullbackCoefficients e (t • θ) w z =
          Real.sin t ^ 2 * inner ℝ w z +
            (t ^ 2 - Real.sin t ^ 2) * inner ℝ w θ * inner ℝ z θ)
    (hfpolar : ∀ (θ w z : EuclideanSpace ℝ (Fin n)), inner ℝ θ θ = 1 →
      ∀ t : ℝ, 0 ≤ t → t < 1 →
        t ^ 2 * h.pullbackCoefficients f (t • θ) w z =
          Real.sin t ^ 2 * inner ℝ w z +
            (t ^ 2 - Real.sin t ^ 2) * inner ℝ w θ * inner ℝ z θ) :
    ∃ F : OpenPartialHomeomorph M N,
      p ∈ F.source ∧ F p = q ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ F F.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ F.symm F.target ∧
      (∀ x ∈ F.source, ∀ v w : TangentSpace (𝓡 n) x,
        g.inner x v w = h.inner (F x)
          (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w)) ∧
      (mfderiv (𝓡 n) (𝓡 n) F p).comp (mfderiv (𝓡 n) (𝓡 n) e 0) =
        mfderiv (𝓡 n) (𝓡 n) f 0 := by
  have hcoeff (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 1)
      (v w : EuclideanSpace ℝ (Fin n)) :
      g.pullbackCoefficients e x v w = h.pullbackCoefficients f x v w := by
    by_cases hx0 : x = 0
    · subst x
      exact (hemetric v w).trans (hfmetric v w).symm
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hr1 : ‖x‖ < 1 := by simpa using hx
    let θ : EuclideanSpace ℝ (Fin n) := ‖x‖⁻¹ • x
    have hθ : inner ℝ θ θ = 1 := by
      simp [θ, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), ne_of_gt hr]
    have hθx : ‖x‖ • θ = x := by simp [θ, smul_smul, ne_of_gt hr]
    have hform := (hepolar θ v w hθ ‖x‖ hr.le hr1).trans
      (hfpolar θ v w hθ ‖x‖ hr.le hr1).symm
    rw [hθx] at hform
    exact mul_left_cancel₀ (ne_of_gt (sq_pos_of_pos hr)) hform
  obtain ⟨A, hA0, hAsub, hAe, hA, hAi⟩ := exists_smooth_inverse_branch
    Metric.isOpen_ball he (fun x hx =>
      bijective_mfderiv_of_spherical_metric g hemetric hepolar hx) (x := 0) (by simp)
  obtain ⟨B, hB0, hBsub, hBf, hB, hBi⟩ := exists_smooth_inverse_branch
    Metric.isOpen_ball hf (fun x hx =>
      bijective_mfderiv_of_spherical_metric h hfmetric hfpolar hx) (x := 0) (by simp)
  have hAp : A 0 = p := (hAe hA0).trans he0
  have hBq : B 0 = q := (hBf hB0).trans hf0
  have hpA : p ∈ A.target := hAp ▸ A.map_source hA0
  have hAip : A.symm p = 0 := by rw [← hAp, A.left_inv hA0]
  let F := A.symm.trans B
  have hF : ContMDiffOn (𝓡 n) (𝓡 n) ∞ F F.source :=
    hB.comp (hAi.mono inter_subset_left) (fun x hx => hx.2)
  have hFi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ F.symm F.target :=
    hA.comp (hBi.mono inter_subset_left) (fun y hy => hy.2)
  have hcenter : (mfderiv (𝓡 n) (𝓡 n) F p).comp
      (mfderiv (𝓡 n) (𝓡 n) e 0) = mfderiv (𝓡 n) (𝓡 n) f 0 := by
    have hAe' : (A : EuclideanSpace ℝ (Fin n) → M) =ᶠ[𝓝 0] e :=
      eventuallyEq_of_mem (A.open_source.mem_nhds hA0) hAe
    have hBf' : (B : EuclideanSpace ℝ (Fin n) → N) =ᶠ[𝓝 0] f :=
      eventuallyEq_of_mem (B.open_source.mem_nhds hB0) hBf
    have hAd : A.MDifferentiable (𝓡 n) (𝓡 n) :=
      ⟨hA.mdifferentiableOn (by simp), hAi.mdifferentiableOn (by simp)⟩
    have hinv := hAd.symm_comp_deriv hA0
    have hchain := mfderiv_comp p
      ((hB.contMDiffAt (B.open_source.mem_nhds
        (show A.symm p ∈ B.source by simpa only [hAip] using hB0))).mdifferentiableAt
          (by simp))
      ((hAi.contMDiffAt (A.open_target.mem_nhds hpA)).mdifferentiableAt (by simp))
    change ((mfderiv (𝓡 n) (𝓡 n) (B ∘ A.symm) p).comp
      (mfderiv (𝓡 n) (𝓡 n) e 0)) = mfderiv (𝓡 n) (𝓡 n) f 0
    rw [hchain, hAip, ← hAe'.mfderiv_eq, ← hBf'.mfderiv_eq,
      ContinuousLinearMap.comp_assoc]
    rw [hAp] at hinv
    rw [hinv, ContinuousLinearMap.comp_id]
  refine ⟨F, ⟨hpA, ?_⟩, ?_, hF, hFi, ?_, hcenter⟩
  · change A.symm p ∈ B.source
    simpa only [hAip] using hB0
  · change B (A.symm p) = q
    rw [hAip, hBq]
  intro x hx v w
  have hyA : A.symm x ∈ A.source := A.map_target hx.1
  have hyB : A.symm x ∈ B.source := hx.2
  have hAe' : (A : EuclideanSpace ℝ (Fin n) → M) =ᶠ[𝓝 (A.symm x)] e :=
    eventuallyEq_of_mem (A.open_source.mem_nhds hyA) hAe
  have hBf' : (B : EuclideanSpace ℝ (Fin n) → N) =ᶠ[𝓝 (A.symm x)] f :=
    eventuallyEq_of_mem (B.open_source.mem_nhds hyB) hBf
  have hpull (u z : EuclideanSpace ℝ (Fin n)) :
      g.pullbackCoefficients A (A.symm x) u z =
        h.pullbackCoefficients B (A.symm x) u z := by
    unfold RiemannianMetric.pullbackCoefficients
    rw [hAe'.mfderiv_eq, hBf'.mfderiv_eq, hAe'.self_of_nhds, hBf'.self_of_nhds]
    exact hcoeff _ (hAsub hyA) u z
  have hAd : A.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨hA.mdifferentiableOn (by simp), hAi.mdifferentiableOn (by simp)⟩
  have hleft (u : TangentSpace (𝓡 n) x) :
      mfderiv (𝓡 n) (𝓡 n) A (A.symm x) (mfderiv (𝓡 n) (𝓡 n) A.symm x u) = u :=
    congrArg (fun L => L u) (hAd.comp_symm_deriv hx.1)
  have hchain := mfderiv_comp x
    ((hB.contMDiffAt (B.open_source.mem_nhds hyB)).mdifferentiableAt (by simp))
    ((hAi.contMDiffAt (A.open_target.mem_nhds hx.1)).mdifferentiableAt (by simp))
  change g.inner x v w = h.inner (B (A.symm x))
    (mfderiv (𝓡 n) (𝓡 n) (B ∘ A.symm) x v)
    (mfderiv (𝓡 n) (𝓡 n) (B ∘ A.symm) x w)
  rw [hchain]
  have hm := hpull (mfderiv (𝓡 n) (𝓡 n) A.symm x v)
    (mfderiv (𝓡 n) (𝓡 n) A.symm x w)
  change g.inner (A (A.symm x))
      (mfderiv (𝓡 n) (𝓡 n) A (A.symm x) (mfderiv (𝓡 n) (𝓡 n) A.symm x v))
      (mfderiv (𝓡 n) (𝓡 n) A (A.symm x) (mfderiv (𝓡 n) (𝓡 n) A.symm x w)) =
    h.inner (B (A.symm x))
      (mfderiv (𝓡 n) (𝓡 n) B (A.symm x) (mfderiv (𝓡 n) (𝓡 n) A.symm x v))
      (mfderiv (𝓡 n) (𝓡 n) B (A.symm x) (mfderiv (𝓡 n) (𝓡 n) A.symm x w)) at hm
  rw [hleft v, hleft w] at hm
  erw [A.right_inv hx.1] at hm
  exact hm

theorem exists_local_isometry_of_unit_curvature
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [T2Space M] [T2Space N] [CompactSpace M] [CompactSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (hsec : ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 →
        D.sectionalCurvature x u v = 1)
    (hsec' : ∀ (x : N) (u v : TangentSpace (𝓡 n) x),
      h.inner x u u * h.inner x v v - (h.inner x u v) ^ 2 ≠ 0 →
        D'.sectionalCurvature x u v = 1)
    (p : M) (q : N) :
    ∃ F : OpenPartialHomeomorph M N,
      p ∈ F.source ∧ F p = q ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ F F.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ F.symm F.target ∧
      ∀ x ∈ F.source, ∀ v w : TangentSpace (𝓡 n) x,
        g.inner x v w = h.inner (F x)
          (mfderiv (𝓡 n) (𝓡 n) F x v) (mfderiv (𝓡 n) (𝓡 n) F x w) := by
  obtain ⟨e, he0, he, hemetric, _, hepolar⟩ := exists_spherical_exponential g D hsec p
  obtain ⟨f, hf0, hf, hfmetric, _, hfpolar⟩ := exists_spherical_exponential h D' hsec' q
  obtain ⟨F, hp, hq, hF, hFi, hmetric, _⟩ :=
    exists_local_isometry_of_spherical_exponentials g h he0 hf0 he hf
      hemetric hfmetric hepolar hfpolar
  exact ⟨F, hp, hq, hF, hFi, hmetric⟩

end PoincareConjecture.SpaceForm
