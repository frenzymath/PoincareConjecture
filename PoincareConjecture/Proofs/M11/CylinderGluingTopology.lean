import PoincareConjecture.Proofs.M11.CylinderTimeCover
import Mathlib.Topology.LocalAtTarget





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Topology
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.Proofs.M11.CylinderTimeCover

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {C : Type v} [TopologicalSpace C] [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
  [IsManifold (𝓡 n) ∞ C] (D : CylinderTimeCover.{u, v, w} F K C)

theorem map_embedding : IsEmbedding D.map := by
  classical
  let := F.chartedSpace
  choose V hVo hV using fun b ↦ isOpen_induced_iff.mp (D.open_time b)
  let U : D.index → TopologicalSpace.Opens F.Point := fun b ↦
    ⟨F.timeFunction ⁻¹' V b, (hVo b).preimage F.time_smooth.continuous⟩
  let j (b : D.index) := Prod.map
    (spacetimeIntervalInclusion (smoothInterval (D.interval b)) (smoothInterval K) (D.subset b))
    (id : C → C)
  apply isEmbedding_of_iSup_eq_top_of_preimage_subset_range D.map D.map_smooth.continuous U
    (V := fun b ↦ (smoothInterval (D.interval b)).Point × C) (iV := j)
  · rintro _ ⟨p, rfl⟩
    obtain ⟨b, hb⟩ := D.covers p.1
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨b, ?_⟩
    change F.timeFunction (D.map p) ∈ V b
    rw [D.map_time]
    change p.1 ∈ Subtype.val ⁻¹' V b
    rw [hV b]
    exact hb
  · intro b
    have hj := (intervalInclusion_embedding intervalSystem K (D.interval b) (D.subset b)).continuous
    exact hj.prodMap continuous_id
  · intro b p hp
    have ht : p.1.val ∈ V b := by
      change F.timeFunction (D.map p) ∈ V b at hp
      rwa [D.map_time] at hp
    have hb : p.1.val ∈ (D.interval b).domain := by
      change p.1 ∈ {t : K.domain | t.val ∈ (D.interval b).domain}
      rw [← hV b]
      exact ht
    exact ⟨(⟨p.1.val, hb⟩, p.2), Prod.ext (Subtype.ext rfl) rfl⟩
  · intro b
    have heq : D.map ∘ j b = (D.cylinder b).toSpacetime :=
      funext fun p ↦ D.map_eq b p.1 p.2
    rw [heq]
    exact (D.cylinder b).embedding

end PoincareConjecture.Proofs.M11.CylinderTimeCover
