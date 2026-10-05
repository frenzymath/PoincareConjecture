import PoincareLib.Topology.Manifold.Surgery.Event.Capping.CappingOverlap
import PoincareLib.Geometry.Riemannian.Connection
import PoincareLib.Geometry.Manifold.Gluing.Smooth
import PoincareLib.Topology.Gluing.Separation

/-!
# Smooth and Hausdorff charts for actual cap attachment

The old-chart and annular attachment maps supply the smooth transitions.
Their closed identification graphs give the Hausdorff quotient needed for
the discarded-side carrier.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u v

namespace PoincareMT.M38

variable {I : Type u} {O : Type v} [TopologicalSpace O]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) O]
  (U : I → Set (EuclideanSpace ℝ (Fin 3))) (hU : ∀ i, IsOpen (U i))
  [∀ i, Nonempty (U i)]
  (e : ∀ i, OpenPartialHomeomorph (U i) O)

/-- Smoothness of the actual partial maps and their inverses suffices for
all the quotient transition maps, including cap interiors on the diagonal. -/
theorem cappingOverlap_smooth
    (hsmooth : ∀ i,
      letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e i) (e i).source ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e i).symm (e i).target) :
    Poincare.Gluing.SmoothOverlap U hU (cappingOverlap e) := by
  intro i j
  by_cases hij : i = j
  · subst j
    letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    change ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (cappingTransition e i i) (cappingTransition e i i).source
    simpa only [cappingTransition_self, OpenPartialHomeomorph.refl_apply,
      OpenPartialHomeomorph.refl_source] using
      (contMDiff_id.contMDiffOn : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (id : U i → U i) Set.univ)
  · letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (hU j).isOpenEmbedding_subtypeVal.singletonChartedSpace
    change ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (cappingTransition e i j) (cappingTransition e i j).source
    simp only [cappingTransition, dif_neg hij, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.symm_source]
    exact (hsmooth j).2.comp ((hsmooth i).1.mono Set.inter_subset_left)
      (fun _ hx => hx.2)

/-- The closed off-diagonal identification graphs, together with the
closed diagonals of the Euclidean patches, make the cap quotient Hausdorff. -/
theorem cappingOverlap_t2
    (hclosed : ∀ i j, i ≠ j → IsClosed {q : U i × U j |
      q.1 ∈ (e i).source ∧ q.2 ∈ (e j).source ∧ e i q.1 = e j q.2}) :
    T2Space (Quotient (cappingOverlap e).setoid) := by
  apply Poincare.Gluing.OverlapSystem.quotient_t2Space
  intro i j
  by_cases hij : i = j
  · subst j
    change IsClosed {q : U i × U i |
      q.1 ∈ (cappingTransition e i i).source ∧ cappingTransition e i i q.1 = q.2}
    simpa [cappingTransition] using (isClosed_eq continuous_fst continuous_snd :
      IsClosed {q : U i × U i | q.1 = q.2})
  · have heq : {q : U i × U j | (cappingOverlap e).Rel ⟨i, q.1⟩ ⟨j, q.2⟩} =
        {q : U i × U j |
          q.1 ∈ (e i).source ∧ q.2 ∈ (e j).source ∧ e i q.1 = e j q.2} := by
      ext q
      exact cappingTransition_graph e hij q.1 q.2
    rw [heq]
    exact hclosed i j hij

end PoincareMT.M38
