import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Gradient









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle



theorem PoincareConjecture.LeviCivitaData.rescaled_smooth_strainer_pair_bounds
    {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    (f h : Fin k → M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i))
    {S : Set M} {δ C : ℝ}
    (hunit : ∀ x ∈ S, ∀ i,
      g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
      g.tangentNorm x (D.gradient (h i) x) ≤ 1)
    (hpair : ∀ x ∈ S, ∀ i,
      g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1 + 2 * δ)
    (hcross : ∀ x ∈ S, ∀ i j, i ≠ j →
      |g.inner x (D.gradient (f i) x) (D.gradient (f j) x)| ≤ δ ∧
      |g.inner x (D.gradient (f i) x) (D.gradient (h j) x)| ≤ δ ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (f j) x)| ≤ δ ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (h j) x)| ≤ δ)
    (htight : ∀ x ∈ S, ∀ i j, i ≠ j →
      g.inner x (D.gradient (f i) x) (D.gradient (f j) x) ≤ 0)
    (hhess : ∀ x ∈ S, ∀ i, ∀ z : TangentSpace (𝓡 n) x,
      D.hessian (f i) x z z ≤ C * g.inner x z z ∧
      D.hessian (h i) x z z ≤ C * g.inner x z z)
    {a : ℝ} (ha : 0 < a) :
    let G := PoincareConjecture.rescaledMetric g a ha
    let DS := PoincareConjecture.rescaledMetric_connection g D a ha
    let F := fun i x => Real.sqrt a * f i x
    let H := fun i x => Real.sqrt a * h i x
    (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (F i)) ∧
      (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (H i)) ∧
      (∀ x ∈ S, ∀ i,
        G.tangentNorm x (DS.gradient (F i) x) ≤ 1 ∧
        G.tangentNorm x (DS.gradient (H i) x) ≤ 1) ∧
      (∀ x ∈ S, ∀ i,
        G.inner x (DS.gradient (F i) x) (DS.gradient (H i) x) ≤ -1 + 2 * δ) ∧
      (∀ x ∈ S, ∀ i j, i ≠ j →
        |G.inner x (DS.gradient (F i) x) (DS.gradient (F j) x)| ≤ δ ∧
        |G.inner x (DS.gradient (F i) x) (DS.gradient (H j) x)| ≤ δ ∧
        |G.inner x (DS.gradient (H i) x) (DS.gradient (F j) x)| ≤ δ ∧
        |G.inner x (DS.gradient (H i) x) (DS.gradient (H j) x)| ≤ δ) ∧
      (∀ x ∈ S, ∀ i j, i ≠ j →
        G.inner x (DS.gradient (F i) x) (DS.gradient (F j) x) ≤ 0) ∧
      ∀ x ∈ S, ∀ i, ∀ z : TangentSpace (𝓡 n) x,
        DS.hessian (F i) x z z ≤ (C / Real.sqrt a) * G.inner x z z ∧
        DS.hessian (H i) x z z ≤ (C / Real.sqrt a) * G.inner x z z := by
  dsimp only
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun _ : M => Real.sqrt a) :=
    contMDiff_const
  refine ⟨fun i => hs.smul (hf i), fun i => hs.smul (hh i), ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx i
    simpa only [PoincareConjecture.LeviCivitaData.gradient_eq_metric_gradient,
      PoincareConjecture.rescaledMetric_tangentNorm_gradient_sqrt_mul] using hunit x hx i
  · intro x hx i
    simpa only [PoincareConjecture.LeviCivitaData.gradient_eq_metric_gradient,
      PoincareConjecture.rescaledMetric_inner_gradient_sqrt_mul] using hpair x hx i
  · intro x hx i j hij
    simpa only [PoincareConjecture.LeviCivitaData.gradient_eq_metric_gradient,
      PoincareConjecture.rescaledMetric_inner_gradient_sqrt_mul] using hcross x hx i j hij
  · intro x hx i j hij
    simpa only [PoincareConjecture.LeviCivitaData.gradient_eq_metric_gradient,
      PoincareConjecture.rescaledMetric_inner_gradient_sqrt_mul] using htight x hx i j hij
  · intro x hx i z
    exact ⟨PoincareConjecture.rescaledMetric_hessian_sqrt_mul_le g D a ha (f i) x z C
      (hhess x hx i z).1,
      PoincareConjecture.rescaledMetric_hessian_sqrt_mul_le g D a ha (h i) x z C
        (hhess x hx i z).2⟩
