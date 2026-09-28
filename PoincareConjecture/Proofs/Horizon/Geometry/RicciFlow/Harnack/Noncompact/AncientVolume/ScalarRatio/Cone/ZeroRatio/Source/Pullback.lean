import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.LocalConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.SourceSmooth








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {Q : Type*} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q] [IsManifold (𝓡 n) ∞ Q]
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]

theorem exists_source_pullback_metrics
    (g : ∀ k, RiemannianMetric n (M k)) (g₀ : RiemannianMetric n Q)
    (V : TopologicalSpace.Opens Q) (A : ∀ k, Q → M k)
    (hA : ∀ᶠ k in atTop, IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (A k) V) :
    ∃ G : ℕ → RiemannianMetric n V,
      ∀ᶠ k in atTop,
        ContMDiff (𝓡 n) (𝓡 n) ∞ (fun y : V => A k y) ∧
        ∀ (x : V) (v w : TangentSpace (𝓡 n) x),
        (G k).inner x v w = (g k).inner (A k x)
          (mfderiv (𝓡 n) (𝓡 n) (fun y : V => A k y) x v)
          (mfderiv (𝓡 n) (𝓡 n) (fun y : V => A k y) x w) := by
  classical
  have hlocal {k : ℕ} (hk : IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (A k) V) :
      IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (fun y : V => A k y) := by
    intro x
    exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) V x).comp (𝓡 n) (M k) (hk x)
  let fallback := g₀.pullbackOfLocalDiffeomorph Subtype.val
    (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) V)
  let G : ℕ → RiemannianMetric n V := fun k =>
    if hk : IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (A k) V then
      (g k).pullbackOfLocalDiffeomorph (fun y : V => A k y) (hlocal hk)
    else fallback
  refine ⟨G, ?_⟩
  filter_upwards [hA] with k hk
  refine ⟨(hlocal hk).contMDiff, fun x v w => ?_⟩
  simp only [G, dif_pos hk, pullbackOfLocalDiffeomorph_inner]



theorem pullbackCoefficients_eq_of_source_metric
    {N P : Type*} [TopologicalSpace N] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) P]
    [IsManifold (𝓡 n) ∞ N] [IsManifold (𝓡 n) ∞ P]
    (g : RiemannianMetric n N) (h : RiemannianMetric n P) (a : P → N)
    (ha : ContMDiff (𝓡 n) (𝓡 n) ∞ a)
    (hmetric : ∀ (x : P) (v w : TangentSpace (𝓡 n) x),
      h.inner x v w = g.inner (a x)
        (mfderiv (𝓡 n) (𝓡 n) a x v) (mfderiv (𝓡 n) (𝓡 n) a x w))
    (φ : EuclideanSpace ℝ (Fin n) → P) {x : EuclideanSpace ℝ (Fin n)}
    (hφ : ContMDiffAt (𝓡 n) (𝓡 n) ∞ φ x) :
    h.pullbackCoefficients φ x = g.pullbackCoefficients (a ∘ φ) x := by
  have hd := mfderiv_comp x (ha.mdifferentiable (by simp) (φ x))
    (hφ.mdifferentiableAt (by simp))
  ext v w
  change h.inner (φ x) (mfderiv (𝓡 n) (𝓡 n) φ x v)
    (mfderiv (𝓡 n) (𝓡 n) φ x w) = _
  rw [hmetric]
  simp only [pullbackCoefficients, hd, ContinuousLinearMap.comp_apply, Function.comp_apply,
    ContinuousLinearMap.bilinearComp_apply]
  rfl



theorem inner_eq_pullback_invFun
    {N P : Type*} [TopologicalSpace N] [TopologicalSpace P] [Nonempty P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) P]
    [IsManifold (𝓡 n) ∞ N] [IsManifold (𝓡 n) ∞ P]
    (g : RiemannianMetric n N) (h : RiemannianMetric n P) (a : P → N)
    (ha : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ a) (hinj : Function.Injective a)
    (hmetric : ∀ (x : P) (v w : TangentSpace (𝓡 n) x),
      h.inner x v w = g.inner (a x)
        (mfderiv (𝓡 n) (𝓡 n) a x v) (mfderiv (𝓡 n) (𝓡 n) a x w))
    {y : N} (hy : y ∈ range a) (v w : TangentSpace (𝓡 n) y) :
    g.inner y v w = h.inner (Function.invFun a y)
      (mfderiv (𝓡 n) (𝓡 n) (Function.invFun a) y v)
      (mfderiv (𝓡 n) (𝓡 n) (Function.invFun a) y w) := by
  have hs := (ChartDistance.contMDiffOn_invFun_of_localDiffeomorph ha hinj).contMDiffAt
    (ha.isOpen_range.mem_nhds hy)
  have heq : a ∘ Function.invFun a =ᶠ[𝓝 y] id := by
    filter_upwards [ha.isOpen_range.mem_nhds hy] with z hz
    exact Function.invFun_eq hz
  have hd := mfderiv_comp y (ha.mdifferentiable (by simp) (Function.invFun a y))
    (hs.mdifferentiableAt (by simp))
  rw [heq.mfderiv_eq, mfderiv_id] at hd
  rw [hmetric, Function.invFun_eq hy]
  have hv := congrArg (fun L => L v) hd
  have hw := congrArg (fun L => L w) hd
  convert! congrArg₂ (fun b c => g.inner y b c) hv hw using 1



theorem iteratedFDeriv_pullbackCoefficients_eq_of_source_metric
    {N P : Type*} [TopologicalSpace N] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) P]
    [IsManifold (𝓡 n) ∞ N] [IsManifold (𝓡 n) ∞ P]
    (g : RiemannianMetric n N) (h : RiemannianMetric n P) (a : P → N)
    (ha : ContMDiff (𝓡 n) (𝓡 n) ∞ a)
    (hmetric : ∀ (x : P) (v w : TangentSpace (𝓡 n) x),
      h.inner x v w = g.inner (a x)
        (mfderiv (𝓡 n) (𝓡 n) a x v) (mfderiv (𝓡 n) (𝓡 n) a x w))
    (φ : EuclideanSpace ℝ (Fin n) → P) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hφ : ContMDiffOn (𝓡 n) (𝓡 n) ∞ φ Ω) (m : ℕ) :
    EqOn (iteratedFDeriv ℝ m (h.pullbackCoefficients φ))
      (iteratedFDeriv ℝ m (g.pullbackCoefficients (a ∘ φ))) Ω := by
  apply Poincare.Analysis.Calculus.eqOn_iteratedFDeriv_of_isOpen hΩ
  intro x hx
  exact pullbackCoefficients_eq_of_source_metric g h a ha hmetric φ
    (hφ.contMDiffAt (hΩ.mem_nhds hx))

end PoincareConjecture.RiemannianMetric
