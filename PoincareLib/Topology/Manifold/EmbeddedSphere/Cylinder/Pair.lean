import PoincareLib.Topology.Manifold.EmbeddedSphere.Relative.Homotopy

/-!
# Vertical homotopy of the local cylinder pair

The neighborhood of the horizontal slice in a slice-plus-exterior model
projects to the slice by a homotopy through maps of pairs. The induced map
on actual relative homology is an isomorphism. Source: Hatcher, Proposition
2.19, p. 118, and M53 derivation 06, for the sphere-separation repair of
Morgan--Tian, Proposition 15.12 and Remark 15.13, p. 365.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex
open Poincare.Topology
open scoped unitInterval

universe u

namespace PoincareMT.Topology.EmbeddedSphere

variable {E : Type u} [TopologicalSpace E] (D : Set E) (t : ℝ)

/-- The slice and its exterior strip inside a cylinder neighborhood.
Source: the local model in M53 derivations 05-06, for Morgan--Tian p. 365. -/
def cylinderSliceNeighborhood : Set (E × ℝ) :=
  {p | (p.2 = 0 ∨ p.1 ∉ D) ∧ |p.2| < t}

/-- Horizontal projection of the slice neighborhood; M53 derivation 06,
using homotopy invariance of pairs in Hatcher, Prop. 2.19, p. 118. -/
def cylinderSliceProjection : C(cylinderSliceNeighborhood D t, E) :=
  ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩

/-- The zero slice lies in the neighborhood when the height is positive.
Source: M53 derivation 06, for Morgan--Tian Proposition 15.12, p. 365. -/
def cylinderSliceInclusion (ht : 0 < t) : C(E, cylinderSliceNeighborhood D t) :=
  ⟨fun u => ⟨(u, 0), Or.inl rfl, by simpa using ht⟩,
    (continuous_id.prodMk continuous_const).subtype_mk _⟩

/-- The height-scaling homotopy from inclusion after projection to the
identity. It leaves the horizontal coordinate unchanged throughout.
Source: M53 derivation 06 and Hatcher, Prop. 2.19, p. 118. -/
def cylinderSliceHomotopy (ht : 0 < t) :
    ContinuousMap.Homotopy
      ((cylinderSliceInclusion D t ht).comp (cylinderSliceProjection D t))
      (ContinuousMap.id (cylinderSliceNeighborhood D t)) where
  toFun q := ⟨(q.2.val.1, (q.1 : ℝ) * q.2.val.2), by
    have hb : |(q.1 : ℝ) * q.2.val.2| ≤ |q.2.val.2| := by
      rw [abs_mul, abs_of_nonneg q.1.property.1]
      exact mul_le_of_le_one_left (abs_nonneg _) q.1.property.2
    refine ⟨?_, hb.trans_lt q.2.property.2⟩
    rcases q.2.property.1 with hz | hu
    · exact Or.inl (by rw [hz, mul_zero])
    · exact Or.inr hu⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp continuous_snd).fst.prodMk
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd).snd)
  map_zero_left x := by
    apply Subtype.ext
    change (x.val.1, (0 : ℝ) * x.val.2) = (x.val.1, 0)
    rw [zero_mul]
  map_one_left x := by
    apply Subtype.ext
    change (x.val.1, (1 : ℝ) * x.val.2) = x.val
    simp only [one_mul, Prod.mk.eta]

/-- The actual horizontal projection induces an isomorphism on relative
homology, with relative subspace the preimage of the horizontal exterior.
Source: Hatcher, Prop. 2.19, p. 118, and M53 derivation 06. -/
theorem cylinderSliceProjection_relative_homology_isIso (ht : 0 < t) (n : Nat) :
    IsIso (homologyMap (integralRelativeMap (cylinderSliceProjection D t)
      (A := (cylinderSliceProjection D t) ⁻¹' Dᶜ) (B := Dᶜ) (fun _ hx => hx)) n) := by
  let HY : ContinuousMap.Homotopy
      ((cylinderSliceProjection D t).comp (cylinderSliceInclusion D t ht))
      (ContinuousMap.id E) :=
    { toFun := fun q => q.2
      continuous_toFun := continuous_snd
      map_zero_left _ := rfl
      map_one_left _ := rfl }
  exact integralRelativeMap_homology_isIso_of_pair_inverse
    (cylinderSliceProjection D t) (cylinderSliceInclusion D t ht)
    (fun _ hx => hx) (fun _ hx => hx) (cylinderSliceHomotopy D t ht) HY
    (fun _ _ hx => hx) (fun _ _ hx => hx) n

/-- The actual zero-slice inclusion is inverse to projection on relative
homology. Source: Hatcher, Prop. 2.19, p. 118, and M53 derivation 06. -/
theorem cylinderSliceInclusion_relative_homology_isIso (ht : 0 < t) (n : Nat) :
    IsIso (homologyMap (integralRelativeMap (cylinderSliceInclusion D t ht)
      (A := Dᶜ) (B := (cylinderSliceProjection D t) ⁻¹' Dᶜ) (fun _ hx => hx)) n) := by
  exact integralRelativeMap_homology_isIso_of_pair_inverse
    (cylinderSliceInclusion D t ht) (cylinderSliceProjection D t)
    (fun _ hx => hx) (fun _ hx => hx) (ContinuousMap.Homotopy.refl _)
    (cylinderSliceHomotopy D t ht) (fun _ _ hx => hx) (fun _ _ hx => hx) n

end PoincareMT.Topology.EmbeddedSphere
