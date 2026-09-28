import PoincareConjecture.Proofs.M35.RawFlow.ParallelTensorProduct
import PoincareConjecture.Proofs.M35.RawFlow.SmoothUpperSupport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M35.Uniqueness

open M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem metricGram_nonneg (g : RiemannianMetric n M) (x : M)
    (u v : TangentSpace (𝓡 n) x) : 0 ≤ metricGram g x u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hi (a b : TangentSpace (𝓡 n) x) : inner ℝ a b = g.inner x a b := rfl
  exact sub_nonneg.mpr (by
    simpa only [hi, pow_two] using real_inner_mul_inner_self_le u v)

theorem curvature_diffusion_with_scalar_barrier (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U)
    (hpos : ∀ y ∈ U, ∀ a b : TangentSpace (𝓡 n) y,
      0 ≤ D.curvatureTensor y a b a b + f y * metricGram g y a b)
    (u v : TangentSpace (𝓡 n) x)
    (hnull : D.curvatureTensor x u v u v + f x * metricGram g x u v = 0) :
    0 ≤ D.tensorLaplacian D.riemannEvaluation x ![u, v, u, v] +
      D.laplacian f x * metricGram g x u v := by
  let S : CovariantTensorEvaluation n M 4 :=
    fun y w => D.riemannEvaluation y w + f y * metricGramEvaluation g y w
  have hR := isSmoothCovariantTensor_riemannEvaluation D
  have hF := isSmoothCovariantTensor_scalar_mul
    (isSmoothCovariantTensor_metricGramEvaluation g) hf
  have hS : IsSmoothCovariantTensor S := by
    constructor
    · intro y
      obtain ⟨A, hA⟩ := hR.1 y
      obtain ⟨B, hB⟩ := hF.1 y
      exact ⟨A + B, fun w => by simp only [add_apply, ← hA, ← hB]; rfl⟩
    · intro V hV X hX
      exact (hR.2 V hV X hX).add (hF.2 V hV X hX)
  have hpair (a b c d : TangentSpace (𝓡 n) x) :
      S x ![a, b, c, d] = S x ![c, d, a, b] := by
    change D.curvatureTensor x a b c d + f x *
        (g.inner x a c * g.inner x b d - g.inner x a d * g.inner x b c) =
      D.curvatureTensor x c d a b + f x *
        (g.inner x c a * g.inner x d b - g.inner x c b * g.inner x d a)
    rw [curvatureTensor_pair_exchange D x a b c d,
      g.symm x c a, g.symm x d b, g.symm x c b, g.symm x d a]
    ring
  have hdiag (y : M) (a b : TangentSpace (𝓡 n) y) :
      S y ![a, b, a, b] = D.curvatureTensor y a b a b + f y * metricGram g y a b := by
    simp only [S, LeviCivitaData.riemannEvaluation, metricGramEvaluation,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, metricGram,
      g.symm y b a, pow_two]
  have h := tensorLaplacian_nonneg_at_sectional_null D hS hU hx hpair
    (fun y hy a b => by rw [hdiag]; exact hpos y hy a b) u v
    (by rw [hdiag]; exact hnull)
  change 0 ≤ D.tensorLaplacian (fun y w =>
    D.riemannEvaluation y w + f y * metricGramEvaluation g y w) x ![u, v, u, v] at h
  rw [tensorLaplacian_add D hR hF, tensorLaplacian_scalar_mul_metricGram D hf] at h
  exact h

theorem curvature_diffusion_with_local_scalar_barrier
    {gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData gE)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ ∞ f x)
    (hpos : ∀ᶠ y in 𝓝 x, ∀ a b : EuclideanSpace ℝ (Fin n),
      0 ≤ D.curvatureTensor y a b a b + f y * metricGram gE y a b)
    (u v : EuclideanSpace ℝ (Fin n))
    (hnull : D.curvatureTensor x u v u v + f x * metricGram gE x u v = 0) :
    0 ≤ D.tensorLaplacian D.riemannEvaluation x ![u, v, u, v] +
      D.laplacian f x * metricGram gE x u v := by
  let a := D.tensorLaplacian D.riemannEvaluation x ![u, v, u, v] +
    D.laplacian f x * metricGram gE x u v
  let b := metricGram gE x u v
  have hb : 0 ≤ b := metricGram_nonneg gE x u v
  by_contra hbad
  have ha : a < 0 := lt_of_not_ge hbad
  let δ := -a / (2 * (b + 1))
  have hδ : 0 < δ := div_pos (neg_pos.mpr ha) (by positivity)
  obtain ⟨q, hq, htouch, hupper, hlap⟩ := exists_smooth_upper_support_laplacian D hf hδ
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp (hpos.and hupper)
  have hshift : ∀ y ∈ U, ∀ c d : TangentSpace (𝓡 n) y,
      0 ≤ D.curvatureTensor y c d c d + q y * metricGram gE y c d := by
    intro y hy c d
    exact ((hUsub hy).1 c d).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (hUsub hy).2 (metricGram_nonneg gE y c d)))
  have h := curvature_diffusion_with_scalar_barrier D
    (contMDiff_iff_contDiff.mpr hq) hU hxU hshift u v (by rw [htouch]; exact hnull)
  have hbound := mul_le_mul_of_nonneg_right hlap hb
  have hδeq : 2 * δ * (b + 1) = -a := by
    dsimp only [δ]
    field_simp
  change 0 ≤ D.tensorLaplacian D.riemannEvaluation x ![u, v, u, v] +
    D.laplacian q x * b at h
  change D.laplacian q x * b ≤ (D.laplacian f x + δ) * b at hbound
  have he : D.tensorLaplacian D.riemannEvaluation x ![u, v, u, v] +
      D.laplacian f x * b = a := rfl
  nlinarith

end PoincareConjecture.M35.Uniqueness
