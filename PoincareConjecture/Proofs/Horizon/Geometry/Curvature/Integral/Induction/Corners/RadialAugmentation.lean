import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.AugmentedPair
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.OppositeCross

noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

theorem PoincareConjecture.LeviCivitaData.augmented_strainer_pair_full_bounds_of_radial_cross
    {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : PoincareConjecture.RiemannianMetric n M} (D : PoincareConjecture.LeviCivitaData g)
    (f h : Fin k → M → ℝ) (u v : M → ℝ)
    (hf : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i))
    (hh : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i))
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    {S : Set M} {δ H : ℝ} (hδ : 0 < δ)
    (hsmall : δ ≤ 1 / (16 * ((k : ℝ) + 1))) (hH : 0 ≤ H)
    (hunit : ∀ x ∈ S,
      g.tangentNorm x (D.gradient u x) ≤ 1 ∧
      g.tangentNorm x (D.gradient v x) ≤ 1 ∧
      ∀ i, g.tangentNorm x (D.gradient (f i) x) ≤ 1 ∧
        g.tangentNorm x (D.gradient (h i) x) ≤ 1)
    (htight : ∀ x ∈ S, ∀ i j, i ≠ j →
      g.inner x (D.gradient (f i) x) (D.gradient (f j) x) ≤ 0)
    (hhess : ∀ x ∈ S, ∀ w : TangentSpace (𝓡 n) x,
      D.hessian u x w w ≤ H * g.inner x w w ∧
      D.hessian v x w w ≤ H * g.inner x w w ∧
      ∀ i, D.hessian (f i) x w w ≤ H * g.inner x w w ∧
        D.hessian (h i) x w w ≤ H * g.inner x w w) :
    let ε := δ / (8 * ((k : ℝ) + 1))
    (∀ x ∈ S,
      g.inner x (D.gradient u x) (D.gradient v x) ≤ -1 + ε ^ 2 / 8 ∧
      ∀ i, g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1 + 2 * ε) →
    (∀ x ∈ S, ∀ i j, i ≠ j →
      |g.inner x (D.gradient (f i) x) (D.gradient (f j) x)| ≤ ε ∧
      |g.inner x (D.gradient (h i) x) (D.gradient (f j) x)| ≤ ε) →
    (∀ x ∈ S, ∀ i j, i ≠ j →
      |g.inner x (D.gradient (h i) x) (D.gradient (h j) x)| ≤ ε) →
    (∀ x ∈ S, ∀ i,
      |g.inner x (D.gradient u x) (D.gradient (f i) x)| ≤ ε / 2 ∧
      |g.inner x (D.gradient u x) (D.gradient (h i) x)| ≤ ε / 2) →
    let a := δ / 4
    let β := a / ((k : ℝ) + 1)
    let F := fun x => (1 - a) * u x + β * ∑ i, h i x
    let G := fun x => (1 - a) * v x + β * ∑ i, h i x
    let f' := Fin.cons F f
    let h' := Fin.cons G h
    (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f' i)) ∧
      (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h' i)) ∧
      (∀ x ∈ S,
        (∀ i,
          (1 - 2 * δ ≤ g.tangentNorm x (D.gradient (f' i) x) ∧
            g.tangentNorm x (D.gradient (f' i) x) ≤ 1) ∧
          (1 - 2 * δ ≤ g.tangentNorm x (D.gradient (h' i) x) ∧
            g.tangentNorm x (D.gradient (h' i) x) ≤ 1) ∧
          g.inner x (D.gradient (f' i) x) (D.gradient (h' i) x) ≤ -1 + 2 * δ) ∧
        (∀ i j, i ≠ j →
          |g.inner x (D.gradient (f' i) x) (D.gradient (f' j) x)| ≤ δ ∧
          |g.inner x (D.gradient (h' i) x) (D.gradient (f' j) x)| ≤ δ ∧
          |g.inner x (D.gradient (h' i) x) (D.gradient (h' j) x)| ≤ δ ∧
          g.inner x (D.gradient (f' i) x) (D.gradient (f' j) x) ≤ 0) ∧
        (∀ i : Fin k,
          g.inner x (D.gradient (f' 0) x) (D.gradient (f' i.succ) x) < 0) ∧
        ∀ w : TangentSpace (𝓡 n) x, ∀ i,
          D.hessian (f' i) x w w ≤ H * g.inner x w w ∧
          D.hessian (h' i) x w w ≤ H * g.inner x w w) ∧
      ∀ x ∈ S, Function.Surjective
        (mfderiv (𝓡 n) 𝓘(ℝ, Fin (k + 1) → ℝ) (fun y i => f' i y) x) := by
  dsimp only
  let ε := δ / (8 * ((k : ℝ) + 1))
  intro hpair holdcross hnegcross hradial
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hδ16 : δ ≤ 1 / 16 := by
    have hmul := (le_div_iff₀ (by positivity : 0 < 16 * ((k : ℝ) + 1))).mp hsmall
    nlinarith [mul_nonneg hk hδ.le]
  have hεδ : ε ≤ δ := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0 < 8 * ((k : ℝ) + 1))).mpr
    nlinarith [mul_nonneg hk hδ.le]
  have hε1 : ε ≤ 1 := by linarith
  have hpairs : ∀ x ∈ S,
      g.inner x (D.gradient u x) (D.gradient v x) ≤ -1 + 2 * ε ∧
      ∀ i, g.inner x (D.gradient (f i) x) (D.gradient (h i) x) ≤ -1 + 2 * ε := by
    intro x hx
    refine ⟨?_, (hpair x hx).2⟩
    have he2 : ε ^ 2 ≤ ε := by nlinarith
    linarith [(hpair x hx).1]
  have hcross : ∀ x ∈ S, ∀ i,
      |g.inner x (D.gradient u x) (D.gradient (f i) x)| ≤ ε ∧
      |g.inner x (D.gradient u x) (D.gradient (h i) x)| ≤ ε ∧
      |g.inner x (D.gradient v x) (D.gradient (f i) x)| ≤ ε ∧
      |g.inner x (D.gradient v x) (D.gradient (h i) x)| ≤ ε := by
    intro x hx i
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    obtain ⟨hu', hv', hold⟩ := hunit x hx
    obtain ⟨hf', hh'⟩ := hold i
    obtain ⟨hur, huhr⟩ := hradial x hx i
    refine ⟨hur.trans (by linarith), huhr.trans (by linarith), ?_, ?_⟩
    · exact Poincare.CurvatureIntegral.abs_inner_opposite_le_of_square_error
        (D.gradient u x) (D.gradient v x) (D.gradient (f i) x)
        hε hu' hv' hf' (hpair x hx).1 hur
    · exact Poincare.CurvatureIntegral.abs_inner_opposite_le_of_square_error
        (D.gradient u x) (D.gradient v x) (D.gradient (h i) x)
        hε hu' hv' hh' (hpair x hx).1 huhr
  exact D.augmented_strainer_pair_full_bounds f h u v hf hh hu hv
    hδ hsmall hH hunit htight hhess hpairs holdcross hnegcross hcross
