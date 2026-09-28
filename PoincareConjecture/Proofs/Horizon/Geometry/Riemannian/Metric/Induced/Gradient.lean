import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Submersion.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle InnerProductSpace

namespace PoincareConjecture.RiemannianMetric

variable {m n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 m) ∞ M] [IsManifold (𝓡 n) ∞ N]



theorem mfderiv_gradient_comp_eq_starProjection
    (g : RiemannianMetric m M) (h : RiemannianMetric n N)
    {F : M → N} {x : M} {f : N → ℝ}
    (hF : MDifferentiableAt (𝓡 m) (𝓡 n) F x)
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f (F x))
    (hmetric : ∀ v w : TangentSpace (𝓡 m) x,
      g.inner x v w = h.inner (F x)
        (mfderiv (𝓡 m) (𝓡 n) F x v) (mfderiv (𝓡 m) (𝓡 n) F x w)) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
      ⟨h.toRiemannianMetric⟩
    letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) (F x)) := by
      unfold TangentSpace
      infer_instance
    mfderiv (𝓡 m) (𝓡 n) F x (g.gradient (f ∘ F) x) =
      (mfderiv (𝓡 m) (𝓡 n) F x).range.starProjection (h.gradient f (F x)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (F x)) := by
    unfold TangentSpace
    infer_instance
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨g.gradient (f ∘ F) x, rfl⟩
  · rintro v ⟨w, rfl⟩
    rw [inner_sub_left]
    change h.inner (F x) (h.gradient f (F x)) (mfderiv (𝓡 m) (𝓡 n) F x w) -
      h.inner (F x) (mfderiv (𝓡 m) (𝓡 n) F x (g.gradient (f ∘ F) x))
        (mfderiv (𝓡 m) (𝓡 n) F x w) = 0
    rw [← hmetric, g.inner_gradient, h.inner_gradient, mvfderiv_comp x hf hF]
    simp only [ContinuousLinearMap.comp_apply, sub_self]



theorem ker_mfderiv_pi_eq_orthogonal_span_gradients
    {ι : Type*} [Fintype ι] (g : RiemannianMetric m M)
    (f : ι → M → ℝ) (hf : ∀ i, ContMDiff (𝓡 m) 𝓘(ℝ, ℝ) ∞ (f i)) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 m) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (mfderiv (𝓡 m) 𝓘(ℝ, ι → ℝ) (fun y i => f i y) x).ker =
      (Submodule.span ℝ (Set.range (fun i => g.gradient (f i) x)))ᗮ := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 m) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ext w
  simp only [LinearMap.mem_ker, Submodule.mem_orthogonal]
  constructor
  · intro h v hv
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
    simp only [sum_inner, real_inner_smul_left]
    apply Finset.sum_eq_zero
    intro i _
    have hi : g.inner x (g.gradient (f i) x) w = 0 := by
      rw [g.inner_gradient, ← Poincare.Geometry.Manifold.mfderiv_pi_apply f hf x w i]
      exact congrFun h i
    change c i * g.inner x (g.gradient (f i) x) w = 0
    rw [hi, mul_zero]
  · intro h
    change mfderiv (𝓡 m) 𝓘(ℝ, ι → ℝ) (fun y i => f i y) x w = (0 : ι → ℝ)
    funext i
    exact (Poincare.Geometry.Manifold.mfderiv_pi_apply f hf x w i).trans
      ((g.inner_gradient (f i) x w).symm.trans
        (h _ (Submodule.subset_span ⟨i, rfl⟩)))

end PoincareConjecture.RiemannianMetric
