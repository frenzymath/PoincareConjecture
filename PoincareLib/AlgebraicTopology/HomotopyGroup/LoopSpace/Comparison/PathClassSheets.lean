import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Bases

/-!
# Sheets of the path-class covering

Endpoint-preserving path classes form the carrier of the universal cover.
Appending paths inside a simply connected neighborhood gives its local
sheets. This file proves the sheet algebra and injectivity of endpoint
projection. Source: Hatcher, Section 1.3, printed pp. 63-65; used in the
cover argument for MT Claim 18.16, p. 430.
-/

set_option autoImplicit false

open Set
open scoped unitInterval

universe u

/-- A point of the path-class cover, before its topology is specified.
Source: Hatcher, Section 1.3, printed p. 64. -/
structure PathClassCover {X : Type u} [TopologicalSpace X] (x₀ : X) where
  /-- The endpoint of the represented paths. -/
  endpoint : X
  /-- The endpoint-preserving homotopy class from the fixed basepoint. -/
  pathClass : Path.Homotopic.Quotient x₀ endpoint

namespace PathClassCover

variable {X : Type u} [TopologicalSpace X] {x₀ : X}

/-- The distinguished point represented by the constant path.
Source: Hatcher, Section 1.3, printed p. 64. -/
def basepoint (x₀ : X) : PathClassCover x₀ :=
  ⟨x₀, Path.Homotopic.Quotient.refl x₀⟩

/-- Appending paths in `U` to a fixed class produces a sheet over `U`.
Source: Hatcher, Section 1.3, printed p. 64. -/
def sheet (U : Set X) (a : PathClassCover x₀) : Set (PathClassCover x₀) :=
  {b | ∃ p : Path a.endpoint b.endpoint,
    (∀ t, p t ∈ U) ∧ b.pathClass = a.pathClass.trans (.mk p)}

/-- Every point in a sheet projects into its defining neighborhood.
Source: Hatcher, Section 1.3, printed p. 64. -/
theorem endpoint_mem_of_mem_sheet {U : Set X} {a b : PathClassCover x₀}
    (hb : b ∈ sheet U a) : b.endpoint ∈ U := by
  obtain ⟨p, hp, _⟩ := hb
  simpa using hp 1

/-- A sheet center lies over the neighborhood whenever its sheet is inhabited.
Source: Hatcher, Section 1.3, printed p. 64. -/
theorem center_mem_of_mem_sheet {U : Set X} {a b : PathClassCover x₀}
    (hb : b ∈ sheet U a) : a.endpoint ∈ U := by
  obtain ⟨p, hp, _⟩ := hb
  simpa using hp 0

/-- A class belongs to its own sheet over any neighborhood of its endpoint.
Source: Hatcher, Section 1.3, printed p. 64. -/
theorem mem_sheet_self {U : Set X} (a : PathClassCover x₀)
    (ha : a.endpoint ∈ U) : a ∈ sheet U a := by
  exact ⟨Path.refl a.endpoint, by simpa using fun _ : I => ha, by simp⟩

/-- Reversing the appended path exchanges two sheet centers.
Source: Hatcher, Section 1.3, printed p. 64. -/
theorem mem_sheet_symm {U : Set X} {a b : PathClassCover x₀}
    (hb : b ∈ sheet U a) : a ∈ sheet U b := by
  obtain ⟨p, hp, he⟩ := hb
  refine ⟨p.symm, fun t => hp (unitInterval.symm t), ?_⟩
  simp [he]

/-- Concatenating two paths within a neighborhood preserves sheet membership.
Source: Hatcher, Section 1.3, printed p. 64. -/
theorem mem_sheet_trans {U : Set X} {a b c : PathClassCover x₀}
    (hb : b ∈ sheet U a) (hc : c ∈ sheet U b) : c ∈ sheet U a := by
  obtain ⟨p, hp, he⟩ := hb
  obtain ⟨q, hq, hf⟩ := hc
  refine ⟨p.trans q, ?_, ?_⟩
  · intro t
    have ht : (p.trans q) t ∈ Set.range p ∪ Set.range q := by
      rw [← Path.trans_range]
      exact Set.mem_range_self t
    rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact hs ▸ hp s
    · exact hs ▸ hq s
  · simp [hf, he]

/-- Any point in a sheet can serve as its center.
Source: Hatcher, Section 1.3, printed p. 64. -/
theorem sheet_eq_of_mem {U : Set X} {a b : PathClassCover x₀}
    (hb : b ∈ sheet U a) : sheet U b = sheet U a := by
  ext c
  exact ⟨mem_sheet_trans hb, mem_sheet_trans (mem_sheet_symm hb)⟩

/-- Shrinking the neighborhood shrinks every sheet with fixed center.
Source: Hatcher, Section 1.3, printed p. 64. -/
theorem sheet_mono {U V : Set X} (hUV : U ⊆ V) (a : PathClassCover x₀) :
    sheet U a ⊆ sheet V a := by
  rintro b ⟨p, hp, he⟩
  exact ⟨p, fun t => hUV (hp t), he⟩

/-- Paths lying in one simply connected set are homotopic in the ambient
space. Source: Hatcher, Section 1.3, printed p. 64. -/
theorem paths_homotopic_in_simplyConnected {U : Set X} (hU : IsSimplyConnected U)
    {x y : X} (p q : Path x y) (hp : ∀ t, p t ∈ U) (hq : ∀ t, q t ∈ U) :
    p.Homotopic q := by
  let : SimplyConnectedSpace U := hU
  have hx : x ∈ U := by simpa using hp 0
  have hy : y ∈ U := by simpa using hp 1
  let p' : Path (⟨x, hx⟩ : U) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let q' : Path (⟨x, hx⟩ : U) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨q t, hq t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  exact (SimplyConnectedSpace.paths_homotopic p' q').map
    ⟨Subtype.val, continuous_subtype_val⟩

/-- Endpoint projection is injective on a simply connected sheet.
Source: Hatcher, Section 1.3, printed p. 64. -/
theorem endpoint_injOn_sheet {U : Set X} (hU : IsSimplyConnected U)
    (a : PathClassCover x₀) : (sheet U a).InjOn endpoint := by
  rintro ⟨x, b⟩ hb ⟨y, c⟩ hc hxy
  change x = y at hxy
  subst y
  obtain ⟨p, hp, he⟩ := hb
  obtain ⟨q, hq, hf⟩ := hc
  have hpq : Path.Homotopic.Quotient.mk p = .mk q :=
    Path.Homotopic.Quotient.eq.mpr (paths_homotopic_in_simplyConnected hU p q hp hq)
  have hbc : b = c := he.trans ((congrArg a.pathClass.trans hpq).trans hf.symm)
  exact congrArg (fun k => PathClassCover.mk x k) hbc

/-- A sheet over a path connected set projects onto that set.
Source: Hatcher, Section 1.3, printed p. 64. -/
theorem endpoint_surjOn_sheet {U : Set X} (hU : IsPathConnected U)
    (a : PathClassCover x₀) (ha : a.endpoint ∈ U) :
    (sheet U a).SurjOn endpoint U := by
  intro y hy
  obtain ⟨p, hp⟩ := hU.joinedIn a.endpoint ha y hy
  exact ⟨⟨y, a.pathClass.trans (.mk p)⟩, ⟨p, hp, rfl⟩, rfl⟩

/-- The image of a nonempty simply connected sheet is exactly its neighborhood.
Source: Hatcher, Section 1.3, printed p. 64. -/
theorem image_sheet {U : Set X} (hU : IsPathConnected U)
    (a : PathClassCover x₀) (ha : a.endpoint ∈ U) : endpoint '' sheet U a = U :=
  Set.Subset.antisymm (by rintro _ ⟨b, hb, rfl⟩; exact endpoint_mem_of_mem_sheet hb)
    (endpoint_surjOn_sheet hU a ha)

end PathClassCover
