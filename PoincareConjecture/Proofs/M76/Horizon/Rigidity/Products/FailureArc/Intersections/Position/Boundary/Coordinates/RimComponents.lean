import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Data.Real.Basic
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Intersections.ProperAnnularRims



set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76

theorem common_collar_zero_trace_on_either_component
    {E Z X : Type*} {Q : Set Z} (S : Bool → Set X)
    (hdis : Disjoint (S false) (S true))
    (c : E × ℝ → X) (rim : Bool → Z → E) (f : Bool → Z → X)
    (hbase : ∀ b z, z ∈ Q → c (rim b z, 0) = f b z)
    (hmark : ∀ b, MapsTo (f b) Q (S b)) (b : Bool) :
    (c '' (((rim false '' Q) ∪ (rim true '' Q)) ×ˢ ({0} : Set ℝ))) ∩ S b =
      f b '' Q := by
  ext x
  constructor
  · rintro ⟨⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩, hx⟩
    have ht0 : t = 0 := ht
    subst t
    rcases hz with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
    · cases b
      · exact ⟨z, hz, (hbase false z hz).symm⟩
      · exact False.elim (disjoint_left.mp hdis
          (hmark false hz) ((hbase false z hz) ▸ hx))
    · cases b
      · exact False.elim (disjoint_left.mp hdis
          ((hbase true z hz) ▸ hx) (hmark true hz))
      · exact ⟨z, hz, (hbase true z hz).symm⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨(rim b z, 0), ⟨?_, rfl⟩, hbase b z hz⟩, hmark b hz⟩
    cases b
    · exact Or.inl ⟨z, hz, rfl⟩
    · exact Or.inr ⟨z, hz, rfl⟩

namespace Dehn.ProtectedAnnulus

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1

theorem proper_annulus_boundary_point_on_rim
    {X : Type*} [TopologicalSpace X] {R : Set X}
    (g : V1 × V2 → X)
    (hproper : ∀ z ∈ source, g z ∈ frontier R ↔ z.1 ∈ sphere (0 : V1) 1)
    {x : X} (hx : x ∈ g '' source) (hxR : x ∈ frontier R) :
    ∃ b : Bool, x ∈ (fun z => g (endpoint b, z)) '' Q := by
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨b, hb⟩ := (mem_sphere_iff_exists_endpoint z.1).mp ((hproper z hz).mp hxR)
  exact ⟨b, z.2, hz.2, congrArg g (Prod.ext hb.symm rfl)⟩

theorem proper_annuli_boundary_point_on_common_rim
    {X : Type*} [TopologicalSpace X] {R : Set X}
    (S : Bool → Set X) (hdis : Disjoint (S false) (S true))
    (g : Bool → V1 × V2 → X)
    (hproper : ∀ i z, ∀ _ : z ∈ source, g i z ∈ frontier R ↔ z.1 ∈ sphere (0 : V1) 1)
    (hmark : ∀ i b, MapsTo (fun z => g i (endpoint b, z)) Q (S b))
    {x : X} (hx : x ∈ g false '' source ∩ g true '' source) (hxR : x ∈ frontier R) :
    ∃ b : Bool, x ∈ ((fun z => g false (endpoint b, z)) '' Q) ∩
      ((fun z => g true (endpoint b, z)) '' Q) := by
  obtain ⟨b, hb⟩ := proper_annulus_boundary_point_on_rim (g false) (hproper false) hx.1 hxR
  obtain ⟨c, hc⟩ := proper_annulus_boundary_point_on_rim (g true) (hproper true) hx.2 hxR
  have hxS (i b : Bool) (hx : x ∈ (fun z => g i (endpoint b, z)) '' Q) : x ∈ S b := by
    obtain ⟨z, hz, rfl⟩ := hx
    exact hmark i b hz
  have hbc : b = c := by
    cases b <;> cases c
    · rfl
    · exact False.elim (disjoint_left.mp hdis (hxS false false hb) (hxS true true hc))
    · exact False.elim (disjoint_left.mp hdis (hxS true false hc) (hxS false true hb))
    · rfl
  exact ⟨b, hb, hbc.symm ▸ hc⟩

end Dehn.ProtectedAnnulus
end PoincareConjecture.M76
