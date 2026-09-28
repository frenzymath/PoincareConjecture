import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import Mathlib.Topology.Order.Compact



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {g : RiemannianMetric 2 S}


theorem curvatureTensorNorm_eq_abs_scalarCurvature (D : LeviCivitaData g) (x : S) :
    D.curvatureTensorNorm x = |D.scalarCurvature x| := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hb (i j) : g.inner x (b i) (b j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  have hd : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 2)), finrank_euclideanSpace]
    simp
  change Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
    (D.curvatureTensor x (b i) (b j) (b k) (b l)) ^ 2) = _
  simp_rw [D.curvatureTensor_eq_half_scalarCurvature x, hb]
  rw [hd]
  norm_num [Fin.sum_univ_two]
  convert Real.sqrt_sq_eq_abs (D.scalarCurvature x) using 2
  ring


theorem continuous_curvatureTensorNorm_surface (D : LeviCivitaData g) :
    Continuous D.curvatureTensorNorm := by
  change Continuous (fun x => D.curvatureTensorNorm x)
  simp_rw [D.curvatureTensorNorm_eq_abs_scalarCurvature]
  exact D.continuous_scalarCurvature.abs


theorem exists_pos_curvatureTensorNorm_le_on_surface (D : LeviCivitaData g)
    {K : Set S} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, D.curvatureTensorNorm x ≤ C := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image D.continuous_curvatureTensorNorm_surface.continuousOn
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx
  exact (hC (mem_image_of_mem _ hx)).trans (le_max_left _ _)


theorem exists_pos_curvatureTensorNorm_le_surface [CompactSpace S] (D : LeviCivitaData g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, D.curvatureTensorNorm x ≤ C := by
  obtain ⟨C, hC, hbound⟩ := D.exists_pos_curvatureTensorNorm_le_on_surface isCompact_univ
  exact ⟨C, hC, fun x => hbound x (mem_univ x)⟩

end PoincareConjecture.LeviCivitaData
