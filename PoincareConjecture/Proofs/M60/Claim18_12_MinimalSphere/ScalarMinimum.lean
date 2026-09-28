import PoincareConjecture.Definitions.M60Area
import PoincareConjecture.Definitions.Ch03.RicciFlow
import Mathlib.Topology.Order.Compact









set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m60ScalarMinimum_isLeast [Nonempty M] {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (hcompact : IsCompact (Set.univ : Set M))
    (hscalar : Continuous D.scalarCurvature) :
    IsLeast (Set.range D.scalarCurvature) (m60ScalarMinimum D) := by
  have hrange : IsCompact (Set.range D.scalarCurvature) := by
    simpa only [Set.image_univ] using hcompact.image hscalar
  exact hrange.isLeast_sInf (Set.range_nonempty _)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in



theorem m60ScalarMinimum_isLeast_of_flow {J : Set ℝ} (F : RicciFlow n M J)
    (hcompact : IsCompact (Set.univ : Set M)) (f : UnitTwoSphere → M)
    (hscalar : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓘(ℝ, ℝ)) ∞
      (fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2) (J ×ˢ Set.univ))
    {t : ℝ} (ht : t ∈ J) :
    IsLeast (Set.range (F.connection t).scalarCurvature)
      (m60ScalarMinimum (F.connection t)) := by
  let : Nonempty M := ⟨f m60SpherePole⟩
  apply m60ScalarMinimum_isLeast (F.connection t) hcompact
  have hslice : Continuous (fun x : M => (t, x)) :=
    continuous_const.prodMk continuous_id
  have hcontinuous : ContinuousOn
      (fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2) (J ×ˢ Set.univ) :=
    ContMDiffOn.continuousOn (I := (𝓘(ℝ, ℝ)).prod (𝓡 n)) (I' := 𝓘(ℝ, ℝ)) hscalar
  exact hcontinuous.comp_continuous hslice (fun _ => ⟨ht, Set.mem_univ _⟩)

end PoincareConjecture
