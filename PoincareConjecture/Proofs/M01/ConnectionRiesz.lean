import PoincareConjecture.Proofs.M01.ConnectionExistenceKoszul
import PoincareConjecture.Definitions.Ch01.Curvature

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.ConnectionExistence

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def metricRieszCLM (g : RiemannianMetric n M) (x : M) :
    (TangentSpace (𝓡 n) x →L[ℝ] ℝ) →L[ℝ] TangentSpace (𝓡 n) x :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  ∑ i, (ContinuousLinearMap.apply ℝ ℝ (b i)).smulRight (b i)

theorem metricRieszCLM_inner (g : RiemannianMetric n M) (x : M)
    (φ : TangentSpace (𝓡 n) x →L[ℝ] ℝ) (v : TangentSpace (𝓡 n) x) :
    g.inner x (metricRieszCLM g x φ) v = φ v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  change inner ℝ
    ((∑ i, (ContinuousLinearMap.apply ℝ ℝ (b i)).smulRight (b i)) φ) v = φ v
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.apply_apply, sum_inner, real_inner_smul_left]
  calc
    (∑ i, φ (b i) * inner ℝ (b i) v) =
        ∑ i, inner ℝ (b i) v * φ (b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact mul_comm _ _
    _ = φ (∑ i, inner ℝ (b i) v • b i) := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
    _ = φ v := congrArg φ (b.sum_repr' v)

theorem metricInner_isInvertible (g : RiemannianMetric n M) (x : M) :
    (g.inner x).IsInvertible := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := metricRieszCLM g x)
  · apply ContinuousLinearMap.ext
    intro φ
    apply ContinuousLinearMap.ext
    intro v
    exact metricRieszCLM_inner g x φ v
  · apply ContinuousLinearMap.ext
    intro v
    apply ext_inner_right ℝ
    intro w
    exact metricRieszCLM_inner g x (g.inner x v) w

noncomputable def metricRiesz (g : RiemannianMetric n M) (x : M)
    (φ : TangentSpace (𝓡 n) x →L[ℝ] ℝ) : TangentSpace (𝓡 n) x :=
  metricRieszCLM g x φ

theorem metricRiesz_inner (g : RiemannianMetric n M) (x : M)
    (φ : TangentSpace (𝓡 n) x →L[ℝ] ℝ) (v : TangentSpace (𝓡 n) x) :
    g.inner x (metricRiesz g x φ) v = φ v := by
  exact metricRieszCLM_inner g x φ v

theorem metricRiesz_unique (g : RiemannianMetric n M) (x : M)
    (v : TangentSpace (𝓡 n) x) (φ : TangentSpace (𝓡 n) x →L[ℝ] ℝ)
    (h : ∀ w, g.inner x v w = φ w) : v = metricRiesz g x φ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro w
  change g.inner x v w = g.inner x (metricRiesz g x φ) w
  rw [metricRiesz_inner]
  exact h w

end PoincareConjecture.ConnectionExistence
