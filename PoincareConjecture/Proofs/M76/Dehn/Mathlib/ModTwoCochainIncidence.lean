import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SimplicialCocycleCover
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.CharP.Two










set_option autoImplicit false

open Set
open scoped BigOperators

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} (A : PreAbstractSimplicialComplex ι)



abbrev Edge := {s : Finset ι // s ∈ A.faces ∧ s.card = 2}



abbrev Triangle := {s : Finset ι // s ∈ A.faces ∧ s.card = 3}

open Classical in


theorem pair_mem_faces {s : Finset ι} (hs : s ∈ A.faces)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) : {i, j} ∈ A.faces :=
  (A.isRelLowerSet_faces hs).2 (by simpa only [Finset.insert_subset_iff,
    Finset.singleton_subset_iff] using And.intro hi hj) (Finset.insert_nonempty i {j})

open Classical in


noncomputable def pairEdge (i j : ι) (hface : {i, j} ∈ A.faces) (hne : i ≠ j) : Edge A :=
  ⟨{i, j}, hface, Finset.card_pair hne⟩



noncomputable def vertexCoboundary : (ι → ZMod 2) →ₗ[ZMod 2] (Edge A → ZMod 2) :=
  LinearMap.pi fun e => ∑ i ∈ e.val, LinearMap.proj i



theorem vertexCoboundary_apply (a : ι → ZMod 2) (e : Edge A) :
    vertexCoboundary A a e = ∑ i ∈ e.val, a i := by
  simp [vertexCoboundary]

open Classical in


theorem vertexCoboundary_pair (a : ι → ZMod 2) (i j : ι)
    (hface : {i, j} ∈ A.faces) (hne : i ≠ j) :
    vertexCoboundary A a (pairEdge A i j hface hne) = a i + a j := by
  rw [vertexCoboundary_apply]
  simp [pairEdge, hne]

variable [Fintype ι]

open Classical in


noncomputable def triangleEdges (t : Triangle A) : Finset (Edge A) :=
  Finset.univ.filter (fun e => e.val ⊆ t.val)



noncomputable def edgeCoboundary : (Edge A → ZMod 2) →ₗ[ZMod 2] (Triangle A → ZMod 2) :=
  LinearMap.pi fun t => ∑ e ∈ triangleEdges A t, LinearMap.proj e



theorem edgeCoboundary_apply (z : Edge A → ZMod 2) (t : Triangle A) :
    edgeCoboundary A z t = ∑ e ∈ triangleEdges A t, z e := by
  simp [edgeCoboundary]

omit [Fintype ι] in
open Classical in
private theorem pair_subset_triple_cases {s : Finset ι} {i j k : ι}
    (hcard : s.card = 2) (hsub : s ⊆ {i, j, k}) :
    s = {i, j} ∨ s = {j, k} ∨ s = {i, k} := by
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hcard
  have ha : a ∈ ({i, j, k} : Finset ι) := hsub (by rw [hs]; simp)
  have hb : b ∈ ({i, j, k} : Finset ι) := hsub (by rw [hs]; simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl
  · rcases hb with rfl | rfl | rfl
    · exact (hab rfl).elim
    · exact Or.inl hs
    · exact Or.inr (Or.inr hs)
  · rcases hb with rfl | rfl | rfl
    · exact Or.inl (hs.trans (Finset.pair_comm _ _))
    · exact (hab rfl).elim
    · exact Or.inr (Or.inl hs)
  · rcases hb with rfl | rfl | rfl
    · exact Or.inr (Or.inr (hs.trans (Finset.pair_comm _ _)))
    · exact Or.inr (Or.inl (hs.trans (Finset.pair_comm _ _)))
    · exact (hab rfl).elim

open Classical in


theorem triangleEdges_eq_three (t : Triangle A) {i j k : ι}
    (ht : t.val = {i, j, k}) (eij ejk eik : Edge A)
    (hij : eij.val = {i, j}) (hjk : ejk.val = {j, k}) (hik : eik.val = {i, k}) :
    triangleEdges A t = {eij, ejk, eik} := by
  ext e
  simp only [triangleEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro he
    rw [ht] at he
    rcases pair_subset_triple_cases e.property.2 he with h | h | h
    · exact Or.inl (Subtype.ext (h.trans hij.symm))
    · exact Or.inr (Or.inl (Subtype.ext (h.trans hjk.symm)))
    · exact Or.inr (Or.inr (Subtype.ext (h.trans hik.symm)))
  · rintro (rfl | rfl | rfl)
    · rw [hij, ht]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl <;> simp
    · rw [hjk, ht]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl <;> simp
    · rw [hik, ht]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      rcases hx with rfl | rfl <;> simp

open Classical in



theorem edgeCoboundary_triangle (z : Edge A → ZMod 2) (t : Triangle A) {i j k : ι}
    (ht : t.val = {i, j, k}) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (eij ejk eik : Edge A)
    (heij : eij.val = {i, j}) (hejk : ejk.val = {j, k}) (heik : eik.val = {i, k}) :
    edgeCoboundary A z t = z eij + z ejk + z eik := by
  have h01 : eij ≠ ejk := by
    intro h
    have hmem := congrArg (fun e : Edge A => i ∈ e.val) h
    simp [heij, hejk, hij, hik] at hmem
  have h02 : eij ≠ eik := by
    intro h
    have hmem := congrArg (fun e : Edge A => j ∈ e.val) h
    simp [heij, heik, hij.symm, hjk] at hmem
  have h12 : ejk ≠ eik := by
    intro h
    have hmem := congrArg (fun e : Edge A => j ∈ e.val) h
    simp [hejk, heik, hij.symm, hjk] at hmem
  rw [edgeCoboundary_apply, triangleEdges_eq_three A t ht eij ejk eik heij hejk heik]
  have he0 : eij ∉ ({ejk, eik} : Finset (Edge A)) := by simp [h01, h02]
  have he1 : ejk ∉ ({eik} : Finset (Edge A)) := by simp [h12]
  rw [Finset.sum_insert he0, Finset.sum_insert he1, Finset.sum_singleton, add_assoc]




theorem edgeCoboundary_vertexCoboundary (a : ι → ZMod 2) :
    edgeCoboundary A (vertexCoboundary A a) = 0 := by
  classical
  funext t
  obtain ⟨i, j, k, hij, hik, hjk, ht⟩ := Finset.card_eq_three.mp t.property.2
  have hi : i ∈ t.val := by rw [ht]; simp
  have hj : j ∈ t.val := by rw [ht]; simp
  have hk : k ∈ t.val := by rw [ht]; simp
  let eij := pairEdge A i j (pair_mem_faces A t.property.1 hi hj) hij
  let ejk := pairEdge A j k (pair_mem_faces A t.property.1 hj hk) hjk
  let eik := pairEdge A i k (pair_mem_faces A t.property.1 hi hk) hik
  rw [edgeCoboundary_triangle A _ t ht hij hik hjk eij ejk eik rfl rfl rfl,
    vertexCoboundary_pair, vertexCoboundary_pair, vertexCoboundary_pair]
  change (a i + a j) + (a j + a k) + (a i + a k) = 0
  calc
    _ = (a i + a i) + (a j + a j) + (a k + a k) := by ac_rfl
    _ = 0 := by simp only [CharTwo.add_self_eq_zero]

end PreAbstractSimplicialComplex.ModTwoCochains
