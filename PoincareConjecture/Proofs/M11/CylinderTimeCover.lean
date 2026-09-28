import PoincareConjecture.Proofs.M11.IntervalProductMaps





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.Proofs.M11

structure CylinderTimeCover {n : ℕ} {X : Type u} [TopologicalSpace X]
    {time : X → ℝ} {I : SpacetimeInterval} (F : GeneralizedFlowSpacetime n X time I)
    (K : SpacetimeInterval) (C : Type v) [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C] where
  index : Type w
  interval : index → SpacetimeInterval
  subset : ∀ b, (interval b).domain ⊆ K.domain
  open_time : ∀ b, IsOpen {t : K.domain | t.val ∈ (interval b).domain}
  covers : ∀ t : K.domain, ∃ b, t.val ∈ (interval b).domain
  cylinder : ∀ b, CompatibleSpacetimeCylinder F (smoothInterval (interval b)) C
  agree : ∀ b c t (hb : t ∈ (interval b).domain) (hc : t ∈ (interval c).domain) x,
    (cylinder b).toSpacetime (⟨t, hb⟩, x) = (cylinder c).toSpacetime (⟨t, hc⟩, x)

namespace CylinderTimeCover

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {F : GeneralizedFlowSpacetime n X time I}
  {C : Type v} [TopologicalSpace C] [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
  [IsManifold (𝓡 n) ∞ C] (D : CylinderTimeCover.{u, v, w} F K C)

noncomputable def map (p : (smoothInterval K).Point × C) : F.Point :=
  (D.cylinder (Classical.choose (D.covers p.1))).toSpacetime
    (⟨p.1.val, Classical.choose_spec (D.covers p.1)⟩, p.2)

theorem map_eq (b : D.index) (t : (smoothInterval (D.interval b)).Point) (x : C) :
    D.map (spacetimeIntervalInclusion (smoothInterval (D.interval b))
      (smoothInterval K) (D.subset b) t, x) = (D.cylinder b).toSpacetime (t, x) := by
  exact D.agree _ b t.val _ t.property x

theorem map_time (p : (smoothInterval K).Point × C) : F.timeFunction (D.map p) = p.1.val :=
  (D.cylinder (Classical.choose (D.covers p.1))).time_eq _

theorem map_smooth : ContMDiff (spacetimeModel n) (spacetimeModel n) ∞ D.map := by
  let := F.chartedSpace
  let := intervalChartedSpace K
  apply interval_product_smooth_of_local K D.interval D.subset D.open_time D.covers
  intro b
  have heq : D.map ∘ Prod.map (spacetimeIntervalInclusion (smoothInterval (D.interval b))
      (smoothInterval K) (D.subset b)) id = (D.cylinder b).toSpacetime :=
    funext fun p ↦ D.map_eq b p.1 p.2
  rw [heq]
  exact (D.cylinder b).smooth

end CylinderTimeCover
end PoincareConjecture.Proofs.M11
