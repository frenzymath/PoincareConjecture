import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Coordinates.TorusCrossingPatch
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.CoordinateRimIntersection

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.PeriodicSquare

local notation "P2" => (ℝ × ℝ)

theorem SourceSquareMap.exists_original_coordinate_rim_patches
    {E V X Z ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace X] [TopologicalSpace Z] {e : ι → OpenPartialHomeomorph X V}
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E} {S : Set X} {Q : Set Z}
    (M : SourceSquareMap p K) (H : K.space ≃ₜ S)
    (F : E → X) (hF : PolyhedralPLInCharts e F K.space)
    (hFval : ∀ x : K.space, F x = (H x : X))
    (h : (AddCircle p × AddCircle p) ≃ₜ S)
    (hvalue : ∀ z : Square p, h (projection p z) = H (M.map z))
    (f : Bool → Z → X) (q : Bool → Q ≃ₜ AddCircle p)
    (hf : ∀ b (z : Q), f b z =
      (h (if b then (((p / 2 : ℝ) : AddCircle p), q b z)
        else (q b z, ((p / 2 : ℝ) : AddCircle p))) : X)) :
    ∀ x ∈ f false '' Q ∩ f true '' Q,
      ∃ d : ℝ, 0 < d ∧ ∃ u : P2 → X,
        PolyhedralPLInCharts e u (Icc (-d) d ×ˢ Icc (-d) d) ∧
        InjOn u (Icc (-d) d ×ˢ Icc (-d) d) ∧
        MapsTo u (Icc (-d) d ×ˢ Icc (-d) d) S ∧ u 0 = x ∧
        (∀ z ∈ Icc (-d) d ×ˢ Icc (-d) d, u z ∈ f false '' Q ↔ z.2 = 0) ∧
        ∀ z ∈ Icc (-d) d ×ˢ Icc (-d) d, u z ∈ f true '' Q ↔ z.1 = 0 := by
  have hp : 0 < p := Fact.out
  let k (b : Bool) (t : AddCircle p) : X :=
    h (if b then (((p / 2 : ℝ) : AddCircle p), t)
      else (t, ((p / 2 : ℝ) : AddCircle p)))
  have himage (b : Bool) : f b '' Q = range (k b) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨q b ⟨z, hz⟩, (hf b ⟨z, hz⟩).symm⟩
    · rintro ⟨t, rfl⟩
      obtain ⟨z, hz⟩ := (q b).surjective t
      exact ⟨z, z.property, (hf b z).trans (congrArg (k b) hz)⟩
  intro x hx
  have hsubimage (b : Bool) : range (fun z : Q => f b z) = f b '' Q := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, z.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  have hcross := (coordinate_rim_intersection h q ((p / 2 : ℝ) : AddCircle p)
    (fun b z => f b z) (hf false) (hf true)).1
  rw [hsubimage false, hsubimage true] at hcross
  have hxcenter := mem_singleton_iff.mp (hcross.subset hx)
  obtain ⟨u, hu, hui, huS, hu0, _, haxis₀, haxis₁⟩ :=
    M.exists_original_coordinate_crossing_patch H F hF hFval h hvalue
  rw [neg_div] at hu hui huS haxis₀ haxis₁
  refine ⟨p / 4, by positivity, u, hu, hui, huS, hu0.trans hxcenter.symm, ?_, ?_⟩
  · intro z hz
    rw [himage false]
    exact haxis₀ z hz
  · intro z hz
    rw [himage true]
    exact haxis₁ z hz

end PoincareConjecture.M76.PeriodicSquare
