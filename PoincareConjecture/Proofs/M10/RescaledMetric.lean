import PoincareConjecture.Proofs.M10.ExponentialDiffeomorph
import PoincareConjecture.Proofs.M10.RescaledExponential
import PoincareConjecture.Proofs.M10.PullbackMetric

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

noncomputable def rescaledExponentialDiffeomorph
    (G : LExponentialGeometry F T τmax p) (τ : ℝ) (hτ : 0 < τ)
    (hsource : (exponentialSliceChart G τ).source = univ)
    (htarget : (exponentialSliceChart G τ).target = univ) :
    Diffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞ :=
  let L := LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin n)) (2 * Real.sqrt τ)⁻¹
    (inv_ne_zero (mul_ne_zero (by norm_num) (Real.sqrt_pos.2 hτ).ne'))
  L.toContinuousLinearEquiv.toDiffeomorph.trans (exponentialSliceDiffeomorph G τ hsource htarget)

set_option backward.isDefEq.respectTransparency false in

theorem rescaledExponentialDiffeomorph_apply
    (G : LExponentialGeometry F T τmax p) (τ : ℝ) (hτ : 0 < τ)
    (hsource : (exponentialSliceChart G τ).source = univ)
    (htarget : (exponentialSliceChart G τ).target = univ)
    (y : EuclideanSpace ℝ (Fin n)) :
    rescaledExponentialDiffeomorph G τ hτ hsource htarget y =
      rescaledExponential G τ y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  change exponentialSliceChart G τ ((2 * Real.sqrt τ)⁻¹ • y) = _
  rw [exponentialSliceChart_apply, map_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem rescaledExponential_pairing
    (G : LExponentialGeometry F T τmax p) {τ : ℝ} (hτ : 0 < τ)
    (hsource : (exponentialSliceChart G τ).source = univ)
    (htarget : (exponentialSliceChart G τ).target = univ)
    (hgram : ∀ x u v : EuclideanSpace ℝ (Fin n),
      pullbackMetricForm (F.metric (T - τ)) (exponentialSliceChart G τ) x u v =
        4 * τ * inner ℝ u v)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricForm (F.metric (T - τ)) (rescaledExponential G τ) x u v =
      inner ℝ u v := by
  let a := (2 * Real.sqrt τ)⁻¹
  let L := (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin n)) a
    (inv_ne_zero (mul_ne_zero (by norm_num) (Real.sqrt_pos.2 hτ).ne'))).toContinuousLinearEquiv
  let E := exponentialSliceDiffeomorph G τ hsource htarget
  have hfun : rescaledExponential G τ = E ∘ L := by
    funext y
    exact (rescaledExponentialDiffeomorph_apply G τ hτ hsource htarget y).symm
  rw [hfun]
  change (F.metric (T - τ)).inner (E (L x))
    (mfderiv (𝓡 n) (𝓡 n) (E ∘ L) x u)
    (mfderiv (𝓡 n) (𝓡 n) (E ∘ L) x v) = _
  have hE := (E.contMDiffAt (x := L x)).mdifferentiableAt (by simp)
  rw [mfderiv_comp_apply x hE L.differentiableAt.mdifferentiableAt,
    mfderiv_comp_apply x hE L.differentiableAt.mdifferentiableAt,
    mfderiv_eq_fderiv, L.fderiv]
  change pullbackMetricForm (F.metric (T - τ)) (exponentialSliceChart G τ)
    (a • x) (a • u) (a • v) = _
  rw [hgram]
  simp only [inner_smul_left, inner_smul_right, conj_trivial]
  dsimp only [a]
  have hs : (Real.sqrt τ) ^ 2 = τ := Real.sq_sqrt hτ.le
  have hn : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.2 hτ).ne'
  field_simp
  rw [hs]
  ring

end PoincareConjecture.M10
