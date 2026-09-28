import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Overlaps.Topology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Quotient.Metric







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} {X : Type v} {Y : ι → Type v}
  [TopologicalSpace X] [∀ i, TopologicalSpace (Y i)]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Y i)]
  [IsManifold (𝓡 3) ∞ X] [∀ i, IsManifold (𝓡 3) ∞ (Y i)]

instance pieceChartedSpace (i : Option ι) :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Piece X Y i) := by
  cases i <;> exact inferInstance

instance pieceIsManifold (i : Option ι) : IsManifold (𝓡 3) ∞ (Piece X Y i) := by
  cases i <;> exact inferInstance

instance pieceSecondCountable [SecondCountableTopology X]
    [∀ i, SecondCountableTopology (Y i)] (i : Option ι) :
    SecondCountableTopology (Piece X Y i) := by
  cases i <;> exact inferInstance

variable (e : ∀ i, OpenPartialHomeomorph X (Y i))
  (hd : Pairwise (fun i j => Disjoint (e i).source (e j).source))
  (hs : ∀ i, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e i) (e i).source)
  (hi : ∀ i, ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e i).symm (e i).target)

omit [IsManifold (𝓡 3) ∞ X] [∀ i, IsManifold (𝓡 3) ∞ (Y i)] in
include hs hi in
theorem overlaps_smooth (i j : Option ι) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ ((overlaps e hd).transition i j)
      ((overlaps e hd).transition i j).source := by
  cases i with
  | none =>
    cases j with
    | none => exact contMDiff_id.contMDiffOn
    | some j => exact hs j
  | some i =>
    cases j with
    | none => exact hi i
    | some j =>
      by_cases h : i = j
      · subst j
        simpa [overlaps, transition] using
          (contMDiff_id : ContMDiff (𝓡 3) (𝓡 3) ∞ (id : Y i → Y i)).contMDiffOn
            (s := Set.univ)
      · change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (capTransition e i j)
          (capTransition e i j).source
        rw [capTransition_source_empty e hd h]
        exact contMDiffOn_empty

end PoincareConjecture.Surgery.Terminal.Gluing
