import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.OriginalCollars





set_option autoImplicit false

open Set Metric Geometry PLAnnularStrip

namespace Dehn.OrientedPolygonCollar

local notation "V2" => (Fin 2 → ℝ)

variable {L d : ℝ} {A : Set V2}

noncomputable def regionChart (B : OrientedPolygonCollar L d A) :
    squareAnnulus L d ≃ₜ ↥(closure B.outer.inside \ B.inner.inside) :=
  B.chart.trans (Homeomorph.setCongr B.carrier)

theorem regionChart_PL (B : OrientedPolygonCollar L d A) : B.regionChart.IsFinitePL := by
  obtain ⟨f, hf, hcf⟩ := B.chart_PL
  exact ⟨f, hf, hcf⟩

theorem boundary_subset_source (B : OrientedPolygonCollar L d A) :
    B.outer.boundary ℝ ⊆ A ∧ B.inner.boundary ℝ ⊆ A := by
  have h := polygon_collar_boundary_subsets B.outer B.inner B.outer_simplicial
    B.outer_injective B.inner_simplicial B.inner_injective B.nested
  exact ⟨h.1.trans B.carrier.symm.subset, h.2.trans B.carrier.symm.subset⟩

end Dehn.OrientedPolygonCollar

namespace PoincareConjecture.M76.Dehn.PairedCircleCollars

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
  {D : OrdinaryIntervalMarkedModel old i} {L d : ℝ}

theorem boundaries_interior (G : PairedCircleCollars D L d) (j : Fin 2) :
    (G.collar j).outer.boundary ℝ ⊆ ball 0 1 ∧
      (G.collar j).inner.boundary ℝ ⊆ ball 0 1 :=
  ⟨(G.collar j).boundary_subset_source.1.trans (G.source_interior j),
    (G.collar j).boundary_subset_source.2.trans (G.source_interior j)⟩

theorem source_cases (G : PairedCircleCollars D L d) :
    closure (G.collar 1).outer.inside ⊆ (G.collar 0).inner.inside ∨
      closure (G.collar 0).outer.inside ⊆ (G.collar 1).inner.inside ∨
      Disjoint (closure (G.collar 0).outer.inside) (closure (G.collar 1).outer.inside) := by
  apply _root_.Dehn.disjoint_polygon_collars_source_cases
    (G.collar 0).outer (G.collar 0).inner (G.collar 1).outer (G.collar 1).inner
    (G.collar 0).outer_simplicial (G.collar 0).outer_injective
    (G.collar 0).inner_simplicial (G.collar 0).inner_injective
    (G.collar 1).outer_simplicial (G.collar 1).outer_injective
    (G.collar 1).inner_simplicial (G.collar 1).inner_injective
    (G.collar 0).nested (G.collar 1).nested
  rw [← (G.collar 0).carrier, ← (G.collar 1).carrier]
  exact G.source_disjoint

end PoincareConjecture.M76.Dehn.PairedCircleCollars
