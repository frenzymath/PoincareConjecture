import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VertexTetrahedronAdjacency
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

set_option autoImplicit false

open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E)

abbrev FaceOfCard (n : ℕ) := {s : Finset E // s ∈ K.faces ∧ s.card = n}

theorem finite_faceOfCard (hK : K.faces.Finite) (n : ℕ) :
    Finite (K.FaceOfCard n) :=
  (hK.subset (fun _ hs => hs.1)).to_subtype

noncomputable def vertexSingletonFaceEquiv : K.vertices ≃ K.FaceOfCard 1 := by
  let f : K.vertices → K.FaceOfCard 1 := fun p =>
    ⟨{p.val}, p.property, Finset.card_singleton p.val⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q h
    exact Subtype.ext (Finset.singleton_injective (congrArg Subtype.val h))
  · intro t
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp t.property.2
    have hpK : p ∈ K.vertices := by
      change {p} ∈ K.faces
      rw [← hp]
      exact t.property.1
    exact ⟨⟨p, hpK⟩, Subtype.ext hp.symm⟩

theorem card_faceOfCard_one : Nat.card (K.FaceOfCard 1) = Nat.card K.vertices :=
  (Nat.card_congr K.vertexSingletonFaceEquiv).symm

def markedFaceEquiv (A : SimplicialComplex ℝ E) (hAK : A ≤ K) (n : ℕ) :
    {s : K.FaceOfCard n // s.val ∈ A.faces} ≃ A.FaceOfCard n where
  toFun s := ⟨s.val.val, s.property, s.val.property.2⟩
  invFun s := ⟨⟨s.val, hAK s.property.1, s.property.2⟩, s.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

def markedVertexEquiv (A : SimplicialComplex ℝ E) (hAK : A ≤ K) :
    {p : K.vertices // p.val ∈ A.vertices} ≃ A.vertices where
  toFun p := ⟨p.val.val, p.property⟩
  invFun p := ⟨⟨p.val, hAK p.property⟩, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Geometry.SimplicialComplex

namespace Fintype

open Classical in

theorem sum_one_two_add_card_subtype {ι : Type*} [Fintype ι] (P : ι → Prop) :
    (∑ i, if P i then 1 else 2) + Nat.card {i // P i} = 2 * Nat.card ι := by
  classical
  have hmark : Nat.card {i // P i} = ∑ i, if P i then 1 else 0 := by
    rw [Nat.subtype_card (Finset.univ.filter P) (by simp), Finset.card_filter]
  rw [hmark, ← Finset.sum_add_distrib]
  calc
    (∑ i, ((if P i then 1 else 2) + if P i then 1 else 0)) = ∑ _i : ι, 2 := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> rfl
    _ = 2 * Nat.card ι := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
        smul_eq_mul, Nat.mul_comm]

end Fintype
