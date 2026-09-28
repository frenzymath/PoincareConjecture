import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Edges.VertexParameters

set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u
variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))

def edgeEndpoint (a : D.EdgeIndex) (terminal : Bool) : D.vertices :=
  if terminal then ⟨(D.edge a.1 a.2).map 1, (D.endpoints_mem_vertices a).2⟩
  else ⟨(D.edge a.1 a.2).map 0, (D.endpoints_mem_vertices a).1⟩

def edgeFromEndpoint (a : D.EdgeIndex) (terminal : Bool) (t : ℝ) : M :=
  (D.edge a.1 a.2).map (if terminal then 1 - t else t)

@[simp] theorem edgeFromEndpoint_zero (a : D.EdgeIndex) (terminal : Bool) :
    D.edgeFromEndpoint a terminal 0 = (D.edgeEndpoint a terminal : M) := by
  cases terminal <;> simp [edgeFromEndpoint, edgeEndpoint]

theorem edgeFromEndpoint_eq (a : D.EdgeIndex) (terminal : Bool) (t : ℝ) :
    D.edgeFromEndpoint a terminal t = (D.edge a.1 a.2).map
      ((if terminal then 1 else 0) + (if terminal then -1 else 1) * t) := by
  cases terminal <;> simp [edgeFromEndpoint, sub_eq_add_neg]

theorem edgeFromEndpoint_image_terminal (a : D.EdgeIndex) (t : ℝ) :
    D.edgeFromEndpoint a true '' Icc 0 t = (D.edge a.1 a.2).map '' Icc (1 - t) 1 := by
  ext q
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, ?_⟩
    simp [edgeFromEndpoint]

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
