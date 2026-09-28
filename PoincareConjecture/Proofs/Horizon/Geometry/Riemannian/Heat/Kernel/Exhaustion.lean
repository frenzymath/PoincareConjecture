import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Exhaustion
import Mathlib.Geometry.Manifold.PartitionOfUnity












set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M]


theorem exists_smooth_compactSupport_cutoffs (g : RiemannianMetric n M) :
    ∃ χ : ℕ → M → ℝ,
      (∀ j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (χ j)) ∧
      (∀ j, HasCompactSupport (χ j)) ∧
      (∀ j x, χ j x ∈ Icc 0 1) ∧
      (∀ s : Set M, IsCompact s → ∀ᶠ j in atTop, EqOn (χ j) 1 s) := by
  classical
  obtain ⟨K⟩ := g.nonempty_compactExhaustion
  let : SigmaCompactSpace M :=
    SigmaCompactSpace_iff_exists_compact_covering.mpr ⟨K, K.isCompact, K.iUnion_eq⟩
  have hcut (j : ℕ) : ∃ f : C^∞⟮𝓡 n, M; 𝓘(ℝ), ℝ⟯,
      EqOn f 0 (interior (K (j + 1)))ᶜ ∧ EqOn f 1 (K j) ∧
      ∀ x, f x ∈ Icc 0 1 := by
    apply exists_contMDiffMap_zero_one_of_isClosed (𝓡 n)
      isOpen_interior.isClosed_compl (K.isCompact j).isClosed
    exact disjoint_compl_left_iff.mpr (K.subset_interior_succ j)
  choose f hf0 hf1 hfb using hcut
  refine ⟨fun j ↦ f j, fun j ↦ (f j).contMDiff, ?_, hfb, ?_⟩
  · intro j
    apply (K.isCompact (j + 1)).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ (K.isCompact (j + 1)).isClosed
    intro x hx
    by_contra hxK
    exact hx (hf0 j (fun hxI ↦ hxK (interior_subset hxI)))
  · intro s hs
    obtain ⟨N, hN⟩ := K.exists_superset_of_isCompact hs
    exact eventually_atTop.mpr ⟨N, fun j hj x hx ↦ hf1 j (K.subset hj (hN hx))⟩






theorem eventually_cutoff_mul_eq_of_hasCompactSupport
    {χ : ℕ → M → ℝ}
    (hχ : ∀ s : Set M, IsCompact s → ∀ᶠ j in atTop, EqOn (χ j) 1 s)
    {f : M → ℝ} (hf : HasCompactSupport f) :
    ∀ᶠ j in atTop, (fun x ↦ χ j x * f x) = f := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hχ (tsupport f) hf.isCompact)
  filter_upwards [eventually_ge_atTop N] with j hj
  funext x
  by_cases hx : x ∈ tsupport f
  · rw [hN j hj hx]
    simp
  · have hxf : f x = 0 := by
      by_contra hne
      exact hx (subset_closure hne)
    simp [hxf]


theorem exists_smooth_compact_sublevel (g : RiemannianMetric n M) :
    ∃ f : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
      (∀ x, 0 ≤ f x) ∧ (∀ R : ℝ, IsCompact {x | f x ≤ R}) := by
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨χ, hχsmooth, hχcompact, hχrange, hχone⟩ :=
    g.exists_smooth_compactSupport_cutoffs
  have hloc : LocallyFinite (fun j ↦ Function.support (fun x ↦ 1 - χ j x)) := by
    intro x
    obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hχone K hK)
    refine ⟨K, hxK, (finite_lt_nat N).subset ?_⟩
    intro j hj
    obtain ⟨y, hy, hyK⟩ := hj
    by_contra hjN
    exact hy (by simp only [hN j (Nat.le_of_not_gt hjN) hyK, Pi.one_apply, sub_self])
  let f : M → ℝ := fun x ↦ ∑ᶠ j, (1 - χ j x)
  have hsmooth : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f :=
    contMDiff_finsum (fun j ↦ contMDiff_const.sub (hχsmooth j)) hloc
  have hnonneg (j : ℕ) (x : M) : 0 ≤ 1 - χ j x := sub_nonneg.mpr (hχrange j x).2
  refine ⟨f, hsmooth, fun x ↦ finsum_nonneg (fun j ↦ hnonneg j x), fun R ↦ ?_⟩
  obtain ⟨N, hNR⟩ := exists_nat_gt R
  have hK : IsCompact (⋃ j ∈ (Finset.range N : Set ℕ), tsupport (χ j)) :=
    (Finset.range N).finite_toSet.isCompact_biUnion (fun j _ ↦ hχcompact j)
  apply hK.of_isClosed_subset (isClosed_le hsmooth.continuous continuous_const)
  intro x hx
  by_contra hxK
  have hxzero (j : ℕ) (hj : j ∈ Finset.range N) : χ j x = 0 := by
    by_contra hne
    exact hxK (mem_iUnion₂.mpr ⟨j, hj, subset_closure hne⟩)
  have hsupp : (Function.support (fun j ↦ 1 - χ j x)).Finite := hloc.point_finite x
  have hrange : Finset.range N ⊆ Set.Finite.toFinset hsupp := by
    intro j hj
    simp only [Set.Finite.mem_toFinset, Function.mem_support, hxzero j hj, sub_zero,
      ne_eq, one_ne_zero, not_false_eq_true]
  have hNf : (N : ℝ) ≤ f x := by
    change (N : ℝ) ≤ ∑ᶠ j, (1 - χ j x)
    rw [finsum_eq_sum _ hsupp]
    calc
      (N : ℝ) = ∑ j ∈ Finset.range N, (1 - χ j x) := by
        calc
          (N : ℝ) = ∑ _j ∈ Finset.range N, (1 : ℝ) := by simp
          _ = _ := Finset.sum_congr rfl (fun j hj ↦ by rw [hxzero j hj, sub_zero])
      _ ≤ ∑ j ∈ Set.Finite.toFinset hsupp, (1 - χ j x) :=
        Finset.sum_le_sum_of_subset_of_nonneg hrange (fun j _ _ ↦ hnonneg j x)
  exact (not_le_of_gt hNR) (hNf.trans hx)

end PoincareConjecture.RiemannianMetric
