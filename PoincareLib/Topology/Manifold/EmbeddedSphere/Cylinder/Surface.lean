import PoincareLib.Topology.Manifold.EmbeddedSphere.Cylinder.Pair
import PoincareLib.AlgebraicTopology.SingularHomology.Relative.IntegralChartSupport

/-!
# The surface inclusion in the cylinder pair

The actual zero-slice inclusion induces a relative homology isomorphism
into the plane-plus-cylinder-exterior pair. This uses the vertical pair
homotopy and open-cover excision, Hatcher, Propositions 2.19 and Theorem
2.20, pp. 118-119. It supplies the surface comparison for the separation
repair of Morgan--Tian, Proposition 15.12 and Remark 15.13, p. 365.
See M53 derivation 06.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex
open Poincare.Topology

universe u

namespace PoincareMT.Topology.EmbeddedSphere

variable {E : Type u} [TopologicalSpace E] (D : Set E) (t : ℝ)

/-- The horizontal slice together with the exterior of the closed cylinder.
Source: M53 derivations 05-06, for Morgan--Tian, p. 365. -/
def cylinderSliceExterior : Set (E × ℝ) :=
  {p | p.2 = 0} ∪ (D ×ˢ Set.Icc (-t) t)ᶜ

/-- The actual horizontal surface map into the slice-plus-exterior pair.
Source: M53 derivation 06, for Morgan--Tian, p. 365. -/
def cylinderSurfaceMap : C(E, cylinderSliceExterior D t) :=
  ⟨fun u => ⟨(u, 0), Or.inl rfl⟩,
    (continuous_id.prodMk continuous_const).subtype_mk _⟩

/-- With a closed horizontal base and positive height, the actual surface
map induces an isomorphism relative to the cylinder exterior. Source:
Hatcher, pp. 118-119, and M53 derivation 06. -/
theorem cylinderSurfaceMap_relative_homology_isIso
    (hD : IsClosed D) (ht : 0 < t) (n : Nat) :
    IsIso (homologyMap (integralRelativeMap (cylinderSurfaceMap D t)
      (A := Dᶜ)
      (B := (Subtype.val : cylinderSliceExterior D t → E × ℝ) ⁻¹'
        (D ×ˢ Set.Icc (-t) t)ᶜ)
      (fun _ hu hp => hu hp.1)) n) := by
  let A := cylinderSliceExterior D t
  let L : Set A := (Subtype.val : A → E × ℝ) ⁻¹' (D ×ˢ Set.Icc (-t) t)ᶜ
  let V : Set A := {a | |a.val.2| < t}
  let B := (cylinderSliceProjection D t) ⁻¹' Dᶜ
  let LV : Set V := (Subtype.val : V → A) ⁻¹' L
  have hL : IsOpen L := (hD.prod isClosed_Icc).isOpen_compl.preimage
    continuous_subtype_val
  have hV : IsOpen V := isOpen_lt
    (continuous_snd.comp continuous_subtype_val).abs continuous_const
  have hcover : L ∪ V = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro a
    rcases a.property with hz | hL
    · right
      change |a.val.2| < t
      rw [hz, abs_zero]
      exact ht
    · exact Or.inl hL
  let e : cylinderSliceNeighborhood D t ≃ₜ V :=
    { toFun := fun x =>
        ⟨⟨x.val, by
          rcases x.property.1 with hz | hu
          · exact Or.inl hz
          · exact Or.inr (fun hp => hu hp.1)⟩, x.property.2⟩
      invFun := fun y => ⟨y.val.val, by
        refine ⟨?_, y.property⟩
        rcases y.val.property with hz | hL
        · exact Or.inl hz
        · right
          intro hu
          exact hL ⟨hu, (abs_lt.mp y.property).1.le, (abs_lt.mp y.property).2.le⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val }
  have he : ∀ x, x ∈ B ↔ e x ∈ LV := by
    intro x
    change x.val.1 ∉ D ↔ x.val ∉ D ×ˢ Set.Icc (-t) t
    constructor
    · exact fun hu hp => hu hp.1
    · intro hp hu
      exact hp ⟨hu, (abs_lt.mp x.property.2).1.le, (abs_lt.mp x.property.2).2.le⟩
  let E := integralRelativeHomeomorphIso e B LV he
  let j := integralRelativeMap (cylinderSliceInclusion D t ht)
    (A := Dᶜ) (B := B) (fun _ hx => hx)
  let f := integralRelativeMap (cylinderSurfaceMap D t)
    (A := Dᶜ) (B := L) (fun _ hu hp => hu hp.1)
  have hj : integralRelativeProjection Dᶜ ≫ j =
      integralChainsFunctor.map (TopCat.ofHom (cylinderSliceInclusion D t ht)) ≫
        integralRelativeProjection B := integralRelativeMap_projection _ _
  have hf : integralRelativeProjection Dᶜ ≫ f =
      integralChainsFunctor.map (TopCat.ofHom (cylinderSurfaceMap D t)) ≫
        integralRelativeProjection L := integralRelativeMap_projection _ _
  have hfactor : j ≫ E.hom ≫ integralPairInclusion L V = f := by
    apply (cancel_epi (integralRelativeProjection Dᶜ)).mp
    rw [← Category.assoc, ← Category.assoc, hj]
    simp only [Category.assoc, E, integralRelativeHomeomorphIso_projection_assoc, hf]
    rw [integralPairInclusion_projection L V]
    simp only [integralSubspaceChains, ← Category.assoc, ← CategoryTheory.Functor.map_comp]
    rfl
  let : IsIso (homologyMap j n) :=
    cylinderSliceInclusion_relative_homology_isIso D t ht n
  let : IsIso (homologyMap (integralPairInclusion L V) n) :=
    integral_open_cover_excision L V hL hV hcover n
  change IsIso (homologyMap f n)
  rw [← hfactor, homologyMap_comp, homologyMap_comp]
  infer_instance

end PoincareMT.Topology.EmbeddedSphere
