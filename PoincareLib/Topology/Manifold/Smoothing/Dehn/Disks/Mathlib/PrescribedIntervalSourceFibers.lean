import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.PrescribedIntervalDiskMap

/-!
# Exact source identifications in a prescribed interval attachment

The full common-edge parameter returned by the disk-map constructor exhausts
the intersection of the two fixed source triangles. Thus source points are
identified exactly along the prescribed interval, with the same parameter.
This is the source-fiber step needed in Dehn039, sections 4 and 8, before
counting double curves of the target map; see Hatcher, printed pp. 56--57.
-/

set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareMT.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "TE" => segment ℝ ((0, 1) : P2) (0, 0)

/-- The actual half-triangle maps returned by the prescribed attachment
identify precisely the original interval points with equal parameters.
No assertion about injectivity of their target disk map is needed. -/
theorem prescribed_interval_source_eq_iff
    {E0 E1 : Type*} [TopologicalSpace E0] [TopologicalSpace E1]
    {S0 W0 : Set E0} {S1 W1 : Set E1}
    (hW0S : W0 ⊆ S0) (hW1S : W1 ⊆ S1)
    (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL)
    (p0 : I01 ≃ₜ W0) (p1 : I01 ≃ₜ W1) (p : I01 ≃ₜ TE)
    (h0 : ∀ t : I01, (n0 ⟨p0 t, hW0S (p0 t).property⟩ : P2) = p t)
    (h1 : ∀ t : I01, (n1 ⟨p1 t, hW1S (p1 t).property⟩ : P2) = p t)
    (x : S0) (y : S1) :
    (n0 x : P2) = n1 y ↔ ∃ t : I01, (x : E0) = p0 t ∧ (y : E1) = p1 t := by
  constructor
  · intro hxy
    have hxE : (n0 x : P2) ∈ TE :=
      region_inter.subset ⟨(n0 x).property, hxy ▸ (n1 y).property⟩
    let t : I01 := p.symm ⟨n0 x, hxE⟩
    have hpt : (p t : P2) = n0 x :=
      congrArg Subtype.val (p.apply_symm_apply ⟨n0 x, hxE⟩)
    refine ⟨t, ?_, ?_⟩
    · exact congrArg Subtype.val
        (n0.injective (Subtype.ext ((h0 t).trans hpt).symm))
    · exact congrArg Subtype.val
        (n1.injective (Subtype.ext ((h1 t).trans (hpt.trans hxy)).symm))
  · rintro ⟨t, hx, hy⟩
    have hx' : x = ⟨p0 t, hW0S (p0 t).property⟩ := Subtype.ext hx
    have hy' : y = ⟨p1 t, hW1S (p1 t).property⟩ := Subtype.ext hy
    rw [hx', hy', h0, h1]

/-- Each common source point has a unique interval parameter. This keeps
the entire source fiber, not just the image of the attaching interval. -/
theorem prescribed_interval_source_existsUnique
    {E0 E1 : Type*} [TopologicalSpace E0] [TopologicalSpace E1]
    {S0 W0 : Set E0} {S1 W1 : Set E1}
    (hW0S : W0 ⊆ S0) (hW1S : W1 ⊆ S1)
    (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL)
    (p0 : I01 ≃ₜ W0) (p1 : I01 ≃ₜ W1) (p : I01 ≃ₜ TE)
    (h0 : ∀ t : I01, (n0 ⟨p0 t, hW0S (p0 t).property⟩ : P2) = p t)
    (h1 : ∀ t : I01, (n1 ⟨p1 t, hW1S (p1 t).property⟩ : P2) = p t)
    (x : S0) (y : S1) (hxy : (n0 x : P2) = n1 y) :
    ∃! t : I01, (x : E0) = p0 t ∧ (y : E1) = p1 t := by
  obtain ⟨t, hx, hy⟩ :=
    (prescribed_interval_source_eq_iff hW0S hW1S n0 n1 p0 p1 p h0 h1 x y).mp hxy
  refine ⟨t, ⟨hx, hy⟩, ?_⟩
  intro s hs
  exact p0.injective (Subtype.ext (hs.1.symm.trans hx))

end PoincareMT.M76.Dehn
