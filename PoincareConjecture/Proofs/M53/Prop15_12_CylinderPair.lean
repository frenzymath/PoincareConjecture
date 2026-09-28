import PoincareConjecture.Proofs.M53.Prop15_12_RelativeHomotopy











set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex
open PoincareConjecture.Proofs.M02.Topology
open scoped unitInterval

universe u

namespace PoincareConjecture.Proofs.M53

variable {E : Type u} [TopologicalSpace E] (D : Set E) (t : ℝ)



def cylinderSliceNeighborhood : Set (E × ℝ) :=
  {p | (p.2 = 0 ∨ p.1 ∉ D) ∧ |p.2| < t}



def cylinderSliceProjection : C(cylinderSliceNeighborhood D t, E) :=
  ⟨fun p => p.val.1, continuous_fst.comp continuous_subtype_val⟩



def cylinderSliceInclusion (ht : 0 < t) : C(E, cylinderSliceNeighborhood D t) :=
  ⟨fun u => ⟨(u, 0), Or.inl rfl, by simpa using ht⟩,
    (continuous_id.prodMk continuous_const).subtype_mk _⟩




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



theorem cylinderSliceInclusion_relative_homology_isIso (ht : 0 < t) (n : Nat) :
    IsIso (homologyMap (integralRelativeMap (cylinderSliceInclusion D t ht)
      (A := Dᶜ) (B := (cylinderSliceProjection D t) ⁻¹' Dᶜ) (fun _ hx => hx)) n) := by
  exact integralRelativeMap_homology_isIso_of_pair_inverse
    (cylinderSliceInclusion D t ht) (cylinderSliceProjection D t)
    (fun _ hx => hx) (fun _ hx => hx) (ContinuousMap.Homotopy.refl _)
    (cylinderSliceHomotopy D t ht) (fun _ _ hx => hx) (fun _ _ hx => hx) n

end PoincareConjecture.Proofs.M53
