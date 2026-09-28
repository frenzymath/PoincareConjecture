import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Bases

set_option autoImplicit false

open Set
open scoped unitInterval

universe u

structure PathClassCover {X : Type u} [TopologicalSpace X] (x₀ : X) where

  endpoint : X

  pathClass : Path.Homotopic.Quotient x₀ endpoint

namespace PathClassCover

variable {X : Type u} [TopologicalSpace X] {x₀ : X}

def basepoint (x₀ : X) : PathClassCover x₀ :=
  ⟨x₀, Path.Homotopic.Quotient.refl x₀⟩

def sheet (U : Set X) (a : PathClassCover x₀) : Set (PathClassCover x₀) :=
  {b | ∃ p : Path a.endpoint b.endpoint,
    (∀ t, p t ∈ U) ∧ b.pathClass = a.pathClass.trans (.mk p)}

theorem endpoint_mem_of_mem_sheet {U : Set X} {a b : PathClassCover x₀}
    (hb : b ∈ sheet U a) : b.endpoint ∈ U := by
  obtain ⟨p, hp, _⟩ := hb
  simpa using hp 1

theorem center_mem_of_mem_sheet {U : Set X} {a b : PathClassCover x₀}
    (hb : b ∈ sheet U a) : a.endpoint ∈ U := by
  obtain ⟨p, hp, _⟩ := hb
  simpa using hp 0

theorem mem_sheet_self {U : Set X} (a : PathClassCover x₀)
    (ha : a.endpoint ∈ U) : a ∈ sheet U a := by
  exact ⟨Path.refl a.endpoint, by simpa using fun _ : I => ha, by simp⟩

theorem mem_sheet_symm {U : Set X} {a b : PathClassCover x₀}
    (hb : b ∈ sheet U a) : a ∈ sheet U b := by
  obtain ⟨p, hp, he⟩ := hb
  refine ⟨p.symm, fun t => hp (unitInterval.symm t), ?_⟩
  simp [he]

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

theorem sheet_eq_of_mem {U : Set X} {a b : PathClassCover x₀}
    (hb : b ∈ sheet U a) : sheet U b = sheet U a := by
  ext c
  exact ⟨mem_sheet_trans hb, mem_sheet_trans (mem_sheet_symm hb)⟩

theorem sheet_mono {U V : Set X} (hUV : U ⊆ V) (a : PathClassCover x₀) :
    sheet U a ⊆ sheet V a := by
  rintro b ⟨p, hp, he⟩
  exact ⟨p, fun t => hUV (hp t), he⟩

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

theorem endpoint_surjOn_sheet {U : Set X} (hU : IsPathConnected U)
    (a : PathClassCover x₀) (ha : a.endpoint ∈ U) :
    (sheet U a).SurjOn endpoint U := by
  intro y hy
  obtain ⟨p, hp⟩ := hU.joinedIn a.endpoint ha y hy
  exact ⟨⟨y, a.pathClass.trans (.mk p)⟩, ⟨p, hp, rfl⟩, rfl⟩

theorem image_sheet {U : Set X} (hU : IsPathConnected U)
    (a : PathClassCover x₀) (ha : a.endpoint ∈ U) : endpoint '' sheet U a = U :=
  Set.Subset.antisymm (by rintro _ ⟨b, hb, rfl⟩; exact endpoint_mem_of_mem_sheet hb)
    (endpoint_surjOn_sheet hU a ha)

end PathClassCover
