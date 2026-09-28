import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteFaceCounts
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.CommonSubcomplexUnion










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


noncomputable def surfaceEulerCount (K : SimplicialComplex ℝ E) : ℤ :=
  (Nat.card (K.FaceOfCard 1) : ℤ) - Nat.card (K.FaceOfCard 2) + Nat.card (K.FaceOfCard 3)



theorem surfaceEulerCount_eq_vertex_counts (K : SimplicialComplex ℝ E) :
    K.surfaceEulerCount = (Nat.card K.vertices : ℤ) -
      Nat.card (PreAbstractSimplicialComplex.ModTwoCochains.Edge
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex) +
      Nat.card (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex) := by
  rw [surfaceEulerCount, K.card_faceOfCard_one,
    Nat.card_congr (K.vertexFaceEquiv 2), Nat.card_congr (K.vertexFaceEquiv 3)]


theorem surfaceEulerCount_eq_two_sub_residual (K : SimplicialComplex ℝ E) {r : ℕ}
    (h : Nat.card K.vertices +
      Nat.card (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex) + r =
      Nat.card (PreAbstractSimplicialComplex.ModTwoCochains.Edge
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2) :
    K.surfaceEulerCount = 2 - (r : ℤ) := by
  rw [K.surfaceEulerCount_eq_vertex_counts]
  omega




theorem residual_lt_of_surfaceEulerCount_lt
    (K L : SimplicialComplex ℝ E) {rK rL : ℕ}
    (hK : Nat.card K.vertices +
      Nat.card (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex) + rK =
      Nat.card (PreAbstractSimplicialComplex.ModTwoCochains.Edge
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2)
    (hL : Nat.card L.vertices +
      Nat.card (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
        L.vertexAbstractComplex.toPreAbstractSimplicialComplex) + rL =
      Nat.card (PreAbstractSimplicialComplex.ModTwoCochains.Edge
        L.vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2)
    (hcount : K.surfaceEulerCount < L.surfaceEulerCount) : rL < rK := by
  have hK' := K.surfaceEulerCount_eq_two_sub_residual hK
  have hL' := L.surfaceEulerCount_eq_two_sub_residual hL
  omega


theorem card_faceOfCard_union_add_inter (K L U : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hL : L.faces.Finite)
    (hU : U.faces = K.faces ∪ L.faces) (n : ℕ) :
    Nat.card (U.FaceOfCard n) + Nat.card ((K ⊓ L).FaceOfCard n) =
      Nat.card (K.FaceOfCard n) + Nat.card (L.FaceOfCard n) := by
  let A := {s : Finset E | s ∈ K.faces ∧ s.card = n}
  let B := {s : Finset E | s ∈ L.faces ∧ s.card = n}
  have hA : A.Finite := hK.subset (fun _ hs => hs.1)
  have hB : B.Finite := hL.subset (fun _ hs => hs.1)
  have hUnion : {s : Finset E | s ∈ U.faces ∧ s.card = n} = A ∪ B := by
    ext s
    simp only [hU, mem_ofPred_eq, mem_union, A, B]
    tauto
  have hInter : {s : Finset E | s ∈ (K ⊓ L).faces ∧ s.card = n} = A ∩ B := by
    ext s
    change ((s ∈ K.faces ∧ s ∈ L.faces) ∧ s.card = n) ↔
      (s ∈ K.faces ∧ s.card = n) ∧ (s ∈ L.faces ∧ s.card = n)
    tauto
  change {s : Finset E | s ∈ U.faces ∧ s.card = n}.ncard +
      {s : Finset E | s ∈ (K ⊓ L).faces ∧ s.card = n}.ncard = A.ncard + B.ncard
  rw [hUnion, hInter]
  exact Set.ncard_union_add_ncard_inter A B hA hB


theorem surfaceEulerCount_union_add_inter (K L U : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hL : L.faces.Finite)
    (hU : U.faces = K.faces ∪ L.faces) :
    U.surfaceEulerCount + (K ⊓ L).surfaceEulerCount =
      K.surfaceEulerCount + L.surfaceEulerCount := by
  have h1 := congrArg (fun n : ℕ => (n : ℤ))
    (card_faceOfCard_union_add_inter K L U hK hL hU 1)
  have h2 := congrArg (fun n : ℕ => (n : ℤ))
    (card_faceOfCard_union_add_inter K L U hK hL hU 2)
  have h3 := congrArg (fun n : ℕ => (n : ℤ))
    (card_faceOfCard_union_add_inter K L U hK hL hU 3)
  simp only [Nat.cast_add] at h1 h2 h3
  dsimp only [surfaceEulerCount]
  omega



theorem surfaceEulerCount_replacement
    (A B C U V : SimplicialComplex ℝ E)
    (hA : A.faces.Finite) (hB : B.faces.Finite) (hC : C.faces.Finite)
    (hU : U.faces = A.faces ∪ B.faces) (hV : V.faces = A.faces ∪ C.faces)
    (hglue : A ⊓ B = A ⊓ C) :
    V.surfaceEulerCount - U.surfaceEulerCount = C.surfaceEulerCount - B.surfaceEulerCount := by
  have hOld := surfaceEulerCount_union_add_inter A B U hA hB hU
  have hNew := surfaceEulerCount_union_add_inter A C V hA hC hV
  rw [hglue] at hOld
  omega



theorem residual_lt_of_replacement
    (A B C U V : SimplicialComplex ℝ E) {rB rC : ℕ}
    (hA : A.faces.Finite) (hB : B.faces.Finite) (hC : C.faces.Finite)
    (hU : U.faces = A.faces ∪ B.faces) (hV : V.faces = A.faces ∪ C.faces)
    (hglue : A ⊓ B = A ⊓ C)
    (hBres : Nat.card B.vertices +
      Nat.card (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
        B.vertexAbstractComplex.toPreAbstractSimplicialComplex) + rB =
      Nat.card (PreAbstractSimplicialComplex.ModTwoCochains.Edge
        B.vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2)
    (hCres : Nat.card C.vertices +
      Nat.card (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
        C.vertexAbstractComplex.toPreAbstractSimplicialComplex) + rC =
      Nat.card (PreAbstractSimplicialComplex.ModTwoCochains.Edge
        C.vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2)
    (htotal : U.surfaceEulerCount < V.surfaceEulerCount) : rC < rB := by
  have hreplacement := surfaceEulerCount_replacement A B C U V hA hB hC hU hV hglue
  have hcount : B.surfaceEulerCount < C.surfaceEulerCount := by omega
  exact residual_lt_of_surfaceEulerCount_lt B C hBres hCres hcount

end Geometry.SimplicialComplex
