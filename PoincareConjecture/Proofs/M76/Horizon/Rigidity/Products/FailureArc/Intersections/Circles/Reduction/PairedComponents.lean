import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.ChartSymmetry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Relation.Model



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

theorem nonempty_both_surface_intersection_components
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid (Fin 3 → ℝ))
    (K : SimplicialComplex ℝ E) (L : SimplicialComplex ℝ F)
    (hK : K.faces.Finite) (hL : L.faces.Finite)
    {f : E → X} {g : F → X}
    (hf : PolyhedralPLInCharts e f K.space) (hg : PolyhedralPLInCharts e g L.space)
    (hfi : InjOn f K.space) (hgi : InjOn g L.space) (Q : Set E) (T : Set F)
    (hrims : ∀ x ∈ K.space, ∀ y ∈ L.space, f x = g y → (x ∈ Q ↔ y ∈ T))
    (hboundary : ∀ y ∈ L.space ∩ T, g y ∈ f '' K.space →
      Nonempty (OriginalSurfacePairChart e (f '' K.space) (g '' L.space) (g y) true))
    (hinterior : ∀ y ∈ L.space \ T, g y ∈ f '' K.space →
      Nonempty (OriginalSurfacePairChart e (f '' K.space) (g '' L.space) (g y) false)) :
    Nonempty (SurfaceIntersectionComponents K.space L.space f g T) ∧
      Nonempty (SurfaceIntersectionComponents L.space K.space g f Q) := by
  refine ⟨nonempty_surface_intersection_components he K L hK hL hf hg hfi hgi T
    hboundary hinterior,?_⟩
  apply nonempty_surface_intersection_components he L K hL hK hg hf hgi hfi Q
  · intro x hx hxy
    obtain ⟨y,hy,hyx⟩ := hxy
    obtain ⟨C⟩ := hboundary y ⟨hy,(hrims x hx.1 y hy hyx.symm).mp hx.2⟩
      ⟨x,hx.1,hyx.symm⟩
    exact hyx ▸ ⟨C.swap⟩
  · intro x hx hxy
    obtain ⟨y,hy,hyx⟩ := hxy
    obtain ⟨C⟩ := hinterior y ⟨hy,fun h => hx.2
      ((hrims x hx.1 y hy hyx.symm).mpr h)⟩ ⟨x,hx.1,hyx.symm⟩
    exact hyx ▸ ⟨C.swap⟩

end PoincareConjecture.M76
