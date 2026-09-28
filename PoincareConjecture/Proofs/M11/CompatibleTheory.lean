import PoincareConjecture.Proofs.M11.WorldlineUniqueness
import PoincareConjecture.Proofs.M11.CylinderGluing
import PoincareConjecture.Proofs.M11.CylinderMetric
import PoincareConjecture.Proofs.M11.SourceRestriction
import PoincareConjecture.Statements.M11CompatibleOperations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.Proofs.M11

theorem adaptedCompatibleTheory {n : ℕ} {X : Type u} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X] (A : AdaptedMetricAtlas n X) :
    CompatibleSpacetimeTheory.{u, v} (adaptedSpacetime A) intervalSystem where
  worldline_unique := adapted_worldline_unique A
  embedding_unique := by
    intro C _ K L e f s hsK hsL source he hf t htK htL x
    exact adapted_embedding_unique A K L e f s hsK hsL source he hf t htK htL x
  embedding_time_restrict := by
    intro C _ K L h e
    exact ⟨embeddingTimeRestrict intervalSystem K L h e, fun _ _ ↦ rfl⟩
  cylinder_time_restrict := by
    intro C _ _ _ K L h e
    exact ⟨cylinderTimeRestrict intervalSystem K L h e, fun _ _ ↦ rfl⟩
  embedding_source_restrict := by
    intro C C' _ _ K e j hj
    exact ⟨embeddingSourceRestrict e j hj, fun _ _ ↦ rfl⟩
  cylinder_open_restrict := by
    intro C _ _ _ K e U
    exact ⟨cylinderOpenRestrict e U, fun _ _ ↦ rfl⟩
  cylinder_glue := by
    intro C _ _ _ K B J hsub ho hc e he
    let D : CylinderTimeCover (adaptedSpacetime A) K C := {
      index := B
      interval := J
      subset := hsub
      open_time := ho
      covers := hc
      cylinder := e
      agree := he
    }
    exact ⟨D.glued, D.glued_eq, D.glued_based⟩
  cylinder_metric := by
    intro C _ _ _ K e
    exact ⟨pulledCylinderMetric e⟩

end PoincareConjecture.Proofs.M11
