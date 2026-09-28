import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bounds.Ricci

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem ricci_lower_bound_of_curvatureTensor_diagonal_lower_bound
    (D : LeviCivitaData g) (x : M) (k : ℝ)
    (hcurv : ∀ u v, k * (g.inner x u u * g.inner x v v -
      (g.inner x u v) ^ 2) ≤ D.curvatureTensor x u v u v)
    (v : TangentSpace (𝓡 n) x) :
    ((n : ℝ) - 1) * k * g.inner x v v ≤ D.ricci x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hb (i) : g.inner x (b i) (b i) = 1 := by
    change inner ℝ (b i) (b i) = 1
    rw [real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow]
  have hparseval : (∑ i, (g.inner x v (b i)) ^ 2) = g.inner x v v := by
    change (∑ i, (inner ℝ v (b i)) ^ 2) = inner ℝ v v
    rw [b.sum_sq_inner_left, real_inner_self_eq_norm_sq]
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
    simp
  calc
    ((n : ℝ) - 1) * k * g.inner x v v =
        ∑ i, k * (g.inner x v v - (g.inner x v (b i)) ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, hparseval]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim,
        nsmul_eq_mul]
      ring
    _ ≤ ∑ i, D.curvatureTensor x v (b i) v (b i) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [hb, mul_one] using hcurv v (b i)
    _ = D.ricci x v v := rfl

theorem exists_pos_curvatureTensor_diagonal_lower_bound_of_compact
    [CompactSpace M] (D : LeviCivitaData g)
    (hsec : ∀ x u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v) :
    ∃ k > 0, ∀ x u v, k * (g.inner x u u * g.inner x v v -
      (g.inner x u v) ^ 2) ≤ D.curvatureTensor x u v u v := by
  classical
  choose k hk hnear using fun x =>
    D.exists_pos_eventually_curvatureTensor_diagonal_lower_bound x (hsec x)
  choose U hUsub hUopen hxU using fun x => mem_nhds_iff.mp (hnear x)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUopen (by
    intro x _
    exact mem_iUnion.mpr ⟨x, hxU x⟩)
  have hfin (s : Finset M) : ∃ c > 0, ∀ x ∈ s, c ≤ k x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert x s hx ih =>
      obtain ⟨c, hc, hcs⟩ := ih
      refine ⟨min (k x) c, lt_min (hk x) hc, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hcs y hy)
  obtain ⟨c, hc, hcs⟩ := hfin s
  refine ⟨c, hc, ?_⟩
  intro x u v
  obtain ⟨y, hys, hxy⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  have hgram : 0 ≤ g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have h := real_inner_mul_inner_self_le u v
    change (g.inner x u v) * (g.inner x u v) ≤
      g.inner x u u * g.inner x v v at h
    nlinarith
  exact (mul_le_mul_of_nonneg_right (hcs y hys) hgram).trans (hUsub y hxy u v)

theorem exists_pos_ricci_lower_bound_of_compact_positive_sectional
    [CompactSpace M] (D : LeviCivitaData g) (hn : 2 ≤ n)
    (hsec : ∀ x u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v) :
    ∃ k > 0, ∀ x v, k * g.inner x v v ≤ D.ricci x v v := by
  obtain ⟨k, hk, hcurv⟩ :=
    D.exists_pos_curvatureTensor_diagonal_lower_bound_of_compact hsec
  refine ⟨((n : ℝ) - 1) * k, mul_pos ?_ hk, ?_⟩
  · have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · intro x v
    exact D.ricci_lower_bound_of_curvatureTensor_diagonal_lower_bound x k (hcurv x) v

end PoincareConjecture.LeviCivitaData
