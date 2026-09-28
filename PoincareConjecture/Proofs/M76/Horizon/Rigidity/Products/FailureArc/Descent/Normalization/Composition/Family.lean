import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.RepairPairs
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Crossings.ProjectedChart







set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ V} {j : V → t.Carrier} {R Fmark : Set M}

structure FiniteMarkedSurfaceRepairs
    (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark) where
  size : ℕ
  window : Fin size → Set s.Carrier
  motion : Fin size → I → t.Carrier ≃ₜ t.Carrier
  small : Fin size → Set t.Carrier
  disjoint : Pairwise (fun k l ↦ Disjoint (window k) (window l))
  continuous : ∀ k, Continuous (fun z : I × t.Carrier ↦ motion k z.1 z.2)
  inverse_continuous : ∀ k, Continuous (fun z : I × t.Carrier ↦ (motion k z.1).symm z.2)
  zero : ∀ k x, motion k 0 x = x
  piecewiseAffine : ∀ k u i j, (t.charts i).symm.trans
    ((motion k u).toOpenPartialHomeomorph.trans (t.charts j)) ∈ piecewiseAffineGroupoid V3
  region : ∀ k u, (motion k u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R
  mark : ∀ k u, (motion k u) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark
  outside : ∀ k u, EqOn (motion k u) id
    ((step.projection ∘ step.inclusion) ⁻¹' window k)ᶜ
  compact : ∀ k, IsCompact (small k)
  small_window : ∀ k, small k ⊆ (step.projection ∘ step.inclusion) ⁻¹' window k
  source_fixed : ∀ k u, EqOn (motion k u) id (D.endpoint '' D.K.space \ small k)
  cover : (fun z : V × V => D.projected z.1) '' D.repairPairs ⊆ ⋃ k, (step.projection ∘ step.inclusion) '' small k
  crossings : ∀ k, ∀ x y : D.K.space, x ≠ y →
    (step.projection ∘ step.inclusion) (motion k 1 (D.endpoint x)) =
      (step.projection ∘ step.inclusion) (motion k 1 (D.endpoint y)) →
    (step.projection ∘ step.inclusion) (motion k 1 (D.endpoint x)) ∈
      (step.projection ∘ step.inclusion) '' (small k ∪ motion k 1 '' small k) →
    ∃ B : ProjectedSourceCrossing s.charts (step.projection ∘ step.inclusion)
      (motion k 1 ∘ D.endpoint) D.K.space (s.projection ⁻¹' R) x y,
      B.chart.source ⊆ window k

end Geometry.OriginalPLTower

