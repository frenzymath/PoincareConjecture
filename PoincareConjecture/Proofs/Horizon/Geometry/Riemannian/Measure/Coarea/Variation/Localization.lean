import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Green.CompactSupport
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.PartitionOfUnity.CompactSupport

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture

universe u v

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_finite_smooth_decomposition_of_isCompactSupport {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hfc : HasCompactSupport f)
    {α : Type v} (U : α → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : tsupport f ⊆ ⋃ i, U i) :
    ∃ (s : Finset (tsupport f)) (c : s → α) (w : s → M → ℝ),
      (∀ i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (w i)) ∧
      (∀ i, HasCompactSupport (w i)) ∧
      (∀ i, tsupport (w i) ⊆ U (c i)) ∧
      ∀ x, ∑ i, w i x = f x := by
  classical
  obtain ⟨s, c, V, -, hV, ρ, -, hρ⟩ :=
    exists_finite_bump_partition (n := n) hfc.isCompact U hU hcover
  refine ⟨s, c, fun i x => ρ i x * f x, fun i => (ρ i).contMDiff.mul hf,
    fun _ => hfc.mul_left, fun i => tsupport_mul_subset_left.trans (hρ i), ?_⟩
  intro x
  by_cases hx : x ∈ tsupport f
  · rw [← Finset.sum_mul]
    have hs := ρ.sum_eq_one (hV hx)
    rw [finsum_eq_sum_of_fintype] at hs
    rw [hs, one_mul]
  · simp [image_eq_zero_of_notMem_tsupport hx]

namespace LeviCivitaData

variable [MeasurableSpace M] [BorelSpace M] {g : RiemannianMetric n M}

theorem integral_mul_laplacian_of_hasCompactSupport
    (D : LeviCivitaData g) {u v : M → ℝ}
    (hu : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ u)
    (hv : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ v)
    (hc : HasCompactSupport u) :
    (∫ x, u x * D.laplacian v x ∂g.volumeMeasure) =
      -(∫ x, g.inner x (D.gradient u x) (D.gradient v x) ∂g.volumeMeasure) := by
  classical
  obtain ⟨s, c, w, hw, hwc, hws, hsum⟩ :=
    exists_finite_smooth_decomposition_of_isCompactSupport hu hc
      (fun i : M => (chartAt (EuclideanSpace ℝ (Fin n)) i).source)
      (fun _ => (chartAt _ _).open_source)
      (fun x _ => mem_iUnion.mpr ⟨x, mem_chart_source _ x⟩)
  have hlocal (i : s) :
      (∫ x, w i x * D.laplacian v x ∂g.volumeMeasure) =
        -(∫ x, g.inner x (D.gradient (w i) x) (D.gradient v x) ∂g.volumeMeasure) :=
    D.integral_mul_laplacian_of_tsupport_subset_chart
      (chartAt (EuclideanSpace ℝ (Fin n)) (c i)).symm
      contMDiffOn_chart_symm contMDiffOn_chart (hw i) hv (hwc i) (hws i)
  have hgrad (x : M) : D.gradient u x = ∑ i, D.gradient (w i) x := by
    calc
      D.gradient u x = D.gradient (fun y => ∑ i, w i y) x :=
        congrArg (fun a : M → ℝ => D.gradient a x) (funext hsum).symm
      _ = _ := ?_
    exact D.gradient_finset_sum Finset.univ w x
      (fun i _ => (hw i x).mdifferentiableAt (by simp))
  calc
    _ = ∫ x, ∑ i, w i x * D.laplacian v x ∂g.volumeMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [← Finset.sum_mul, hsum]
    _ = ∑ i, ∫ x, w i x * D.laplacian v x ∂g.volumeMeasure :=
      integral_finsetSum _ (fun i _ => D.integrable_mul_laplacian (hw i) hv (hwc i))
    _ = -(∑ i, ∫ x, g.inner x (D.gradient (w i) x) (D.gradient v x)
        ∂g.volumeMeasure) := by simp only [hlocal, Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i, g.inner x (D.gradient (w i) x) (D.gradient v x)
        ∂g.volumeMeasure) := by
      rw [integral_finsetSum _ (fun i _ => D.integrable_inner_gradient (hw i) hv (hwc i))]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only
        rw [hgrad, map_sum, sum_apply]

end LeviCivitaData

end PoincareConjecture
