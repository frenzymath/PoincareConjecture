import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.EndCut.Component
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.Topology









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.StrongHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T}

theorem coordinatePrefix_subset_carrier (horn : StrongHorn E epsilon)
    {b : ℝ} (hb : b < 1) : horn.coordinatePrefix b ⊆ horn.carrier := by
  rintro x ⟨⟨s, t⟩, ⟨_, ht0, htb⟩, rfl⟩
  have h := (horn.coordinate (s, ⟨t, ht0, htb.trans_lt hb⟩)).property
  rwa [horn.coordinate_eq] at h

theorem mem_coordinatePrefix_iff (horn : StrongHorn E epsilon)
    {b : ℝ} (hb : b < 1) (x : horn.carrier) :
    (x : (E.extended.slice T).carrier) ∈ horn.coordinatePrefix b ↔ horn.coordinateHeight x ≤ b := by
  constructor
  · rintro ⟨⟨s, t⟩, ⟨_, ht0, htb⟩, heq⟩
    have hcoord : horn.coordinate (s, ⟨t, ht0, htb.trans_lt hb⟩) = x :=
      Subtype.ext ((horn.coordinate_eq _).trans heq)
    rw [← hcoord]
    simpa [coordinateHeight] using htb
  · intro hx
    exact ⟨((horn.coordinate.symm x).1, ((horn.coordinate.symm x).2 : ℝ)),
      ⟨mem_univ _, (horn.coordinate.symm x).2.property.1, hx⟩,
      horn.parameterization_coordinate_symm x⟩



theorem mem_interior_coordinatePrefix (horn : StrongHorn E epsilon)
    {b : ℝ} (hb : b < 1) (x : horn.carrier)
    (hboundary : (x : (E.extended.slice T).carrier) ∉ horn.boundary_sphere)
    (hx : horn.coordinateHeight x < b) :
    (x : (E.extended.slice T).carrier) ∈ interior (horn.coordinatePrefix b) := by
  let A : Set horn.carrier := {y | horn.coordinateHeight y < b}
  have hA : IsOpen A := isOpen_lt horn.continuous_coordinateHeight continuous_const
  obtain ⟨V, hV, hAV⟩ := hA.image_val
  have hxV : (x : (E.extended.slice T).carrier) ∈ V := by
    have h := mem_image_of_mem Subtype.val (show x ∈ A from hx)
    rw [hAV] at h
    exact h.1
  apply mem_interior_iff_mem_nhds.mpr
  apply mem_of_superset ((hV.inter horn.isOpen_carrier_diff_boundary).mem_nhds
    ⟨hxV, x.property, hboundary⟩)
  intro y hy
  have hyA : y ∈ Subtype.val '' A := by rw [hAV]; exact ⟨hy.1, hy.2.1⟩
  obtain ⟨z, hz, rfl⟩ := hyA
  exact (horn.mem_coordinatePrefix_iff hb z).mpr (le_of_lt hz)



theorem mem_interior_coordinatePrefix_of_scalar_bounds (horn : StrongHorn E epsilon)
    {b lower upper : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hboundary : ∀ x ∈ horn.boundary_sphere,
      (E.extended.connection T).scalarCurvature x ≤ lower)
    (hsection : ∀ x ∈ horn.coordinateSection b,
      upper ≤ (E.extended.connection T).scalarCurvature x)
    {x : (E.extended.slice T).carrier} (hx : x ∈ horn.coordinatePrefix b)
    (hlower : lower < (E.extended.connection T).scalarCurvature x)
    (hupper : (E.extended.connection T).scalarCurvature x < upper) :
    x ∈ interior (horn.coordinatePrefix b) := by
  let x' : horn.carrier := ⟨x, horn.coordinatePrefix_subset_carrier hb1 hx⟩
  apply horn.mem_interior_coordinatePrefix hb1 x'
  · exact fun h => (not_le_of_gt hlower) (hboundary x h)
  · have hle := (horn.mem_coordinatePrefix_iff hb1 x').mp hx
    apply lt_of_le_of_ne hle
    intro heq
    have hxs := (horn.mem_coordinateSection_iff hb0 hb1 x').mpr heq
    exact (not_le_of_gt hupper) (hsection x hxs)

end PoincareConjecture.StrongHorn
