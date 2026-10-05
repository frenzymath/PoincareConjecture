import PoincareLib.AlgebraicTopology.FundamentalGroup.PathMaps
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.PathClassTopology

/-!
# Functorial maps of path-class covers

Continuous maps act on path classes and continuously on their sheet
topologies. If the base is already simply connected, endpoint projection
is a homeomorphism. These facts give the explicit path lifts in the
universal-cover construction. Source: Hatcher, Section 1.3, printed
pp. 63-65; used for MT Claim 18.16, p. 430.
-/

set_option autoImplicit false

open Set TopologicalSpace

universe u v

namespace PathClassCover

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {x₀ : X}

/-- Postcompose the represented path by a continuous map.
Source: Hatcher, Section 1.3, printed pp. 63-65. -/
def map (f : C(X, Y)) (a : PathClassCover x₀) : PathClassCover (f x₀) :=
  ⟨f a.endpoint, a.pathClass.map f⟩

/-- The map of path-class spaces preserves their distinguished points.
Source: Hatcher, Section 1.3, printed pp. 63-65. -/
@[simp] theorem map_basepoint (f : C(X, Y)) : map f (basepoint x₀) = basepoint (f x₀) := rfl

/-- A sheet whose neighborhood maps into `V` maps into the corresponding
sheet over `V`. Source: Hatcher, Section 1.3, printed pp. 63-65. -/
theorem map_mem_sheet (f : C(X, Y)) {U : Set X} {V : Set Y}
    (hUV : U ⊆ f ⁻¹' V) {a b : PathClassCover x₀} (hb : b ∈ sheet U a) :
    map f b ∈ sheet V (map f a) := by
  obtain ⟨p, hp, he⟩ := hb
  refine ⟨p.map f.continuous, fun t => hUV (hp t), ?_⟩
  change b.pathClass.map f = (a.pathClass.map f).trans (.mk (p.map f.continuous))
  rw [he, Path.Homotopic.Quotient.map_trans]
  rfl

/-- Postcomposition is continuous in the path-class sheet topologies.
Source: Hatcher, Section 1.3, printed pp. 63-65. -/
theorem continuous_map [LocallySimplyConnectedSpace X] (f : C(X, Y)) :
    Continuous (map (x₀ := x₀) f) := by
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨V, b, hV, hscV, hb, rfl⟩
  apply (isTopologicalBasis x₀).isOpen_iff.mpr
  intro a ha
  have hfa : map f a ∈ sheet V b := ha
  obtain ⟨U, hU, hscU, haU, hUV⟩ :=
    LocallySimplyConnectedSpace.exists_open_simplyConnected a.endpoint (f ⁻¹' V)
      (by change f a.endpoint ∈ V; exact endpoint_mem_of_mem_sheet hfa)
      (hV.preimage f.continuous)
  refine ⟨sheet U a, ⟨U, a, hU, hscU, haU, rfl⟩, mem_sheet_self a haU, ?_⟩
  intro c hc
  change map f c ∈ sheet V b
  rw [← sheet_eq_of_mem ha]
  exact map_mem_sheet f hUV hc

/-- Every point of a path connected base is reached by endpoint projection.
Source: Hatcher, Section 1.3, printed p. 64. -/
theorem endpoint_surjective [PathConnectedSpace X] (x₀ : X) :
    Function.Surjective (endpoint : PathClassCover x₀ → X) :=
  fun x => ⟨⟨x, .mk (PathConnectedSpace.somePath x₀ x)⟩, rfl⟩

/-- A simply connected base has just one path class over each endpoint.
Source: Hatcher, Section 1.3, printed p. 64. -/
theorem endpoint_injective [SimplyConnectedSpace X] (x₀ : X) :
    Function.Injective (endpoint : PathClassCover x₀ → X) := by
  rintro ⟨x, a⟩ ⟨y, b⟩ h
  change x = y at h
  subst y
  exact congrArg (fun k => PathClassCover.mk x k) (Subsingleton.elim a b)

/-- Endpoint projection is a homeomorphism when the base is already simply
connected. Source: Hatcher, Section 1.3, printed p. 64. -/
noncomputable def endpointHomeomorph [LocallySimplyConnectedSpace X] [SimplyConnectedSpace X]
    (x₀ : X) : PathClassCover x₀ ≃ₜ X :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective endpoint ⟨endpoint_injective x₀, endpoint_surjective x₀⟩)
    (continuous_endpoint x₀) (isOpenMap_endpoint x₀)

/-- The endpoint homeomorphism has the literal endpoint projection as its map.
Source: Hatcher, Section 1.3, printed p. 64. -/
@[simp] theorem endpointHomeomorph_apply [LocallySimplyConnectedSpace X] [SimplyConnectedSpace X]
    (x₀ : X) (a : PathClassCover x₀) : endpointHomeomorph x₀ a = a.endpoint := rfl

end PathClassCover
