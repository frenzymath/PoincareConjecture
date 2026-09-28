import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ModTwoCochainIncidence
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false

open Set
open scoped BigOperators

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} (A : PreAbstractSimplicialComplex ι)

open Classical in

noncomputable def edgeValue (z : Edge A → ZMod 2) (i j : ι) : ZMod 2 :=
  if hij : i = j then 0 else
    if hface : {i, j} ∈ A.faces then z (pairEdge A i j hface hij) else 0

theorem edgeValue_self (z : Edge A → ZMod 2) (i : ι) : edgeValue A z i i = 0 := by
  simp [edgeValue]

open Classical in

theorem edgeValue_pair (z : Edge A → ZMod 2) (i j : ι)
    (hface : {i, j} ∈ A.faces) (hne : i ≠ j) :
    edgeValue A z i j = z (pairEdge A i j hface hne) := by
  simp only [edgeValue, dif_neg hne, dif_pos hface]

theorem edgeValue_symm (z : Edge A → ZMod 2) (i j : ι) :
    edgeValue A z i j = edgeValue A z j i := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  · by_cases hface : {i, j} ∈ A.faces
    · have hface' : {j, i} ∈ A.faces := (Finset.pair_comm i j) ▸ hface
      rw [edgeValue_pair A z i j hface hij, edgeValue_pair A z j i hface' (Ne.symm hij)]
      exact congrArg z (Subtype.ext (Finset.pair_comm i j))
    · have hface' : {j, i} ∉ A.faces := (Finset.pair_comm i j) ▸ hface
      simp only [edgeValue, dif_neg hij, dif_neg (Ne.symm hij), dif_neg hface,
        dif_neg hface']

variable [Fintype ι]

theorem edgeValue_compose (z : Edge A → ZMod 2) (hz : edgeCoboundary A z = 0)
    {s : Finset ι} (hs : s ∈ A.faces) {i j k : ι}
    (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) :
    edgeValue A z i j + edgeValue A z j k = edgeValue A z i k := by
  classical
  by_cases hij : i = j
  · subst j
    rw [edgeValue_self, zero_add]
  by_cases hjk : j = k
  · subst k
    rw [edgeValue_self, add_zero]
  by_cases hik : i = k
  · subst k
    rw [edgeValue_self, edgeValue_symm A z j i, CharTwo.add_self_eq_zero]
  have htri : {i, j, k} ∈ A.faces :=
    (A.isRelLowerSet_faces hs).2 (by
      simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using
        And.intro hi (And.intro hj hk)) (Finset.insert_nonempty _ _)
  let t : Triangle A := ⟨{i, j, k}, htri, by simp [hij, hik, hjk]⟩
  have hfaceij := pair_mem_faces A hs hi hj
  have hfacejk := pair_mem_faces A hs hj hk
  have hfaceik := pair_mem_faces A hs hi hk
  let eij := pairEdge A i j hfaceij hij
  let ejk := pairEdge A j k hfacejk hjk
  let eik := pairEdge A i k hfaceik hik
  have hzt : edgeCoboundary A z t = 0 := congrFun hz t
  rw [edgeCoboundary_triangle A z t rfl hij hik hjk eij ejk eik rfl rfl rfl] at hzt
  rw [edgeValue_pair A z i j hfaceij hij, edgeValue_pair A z j k hfacejk hjk,
    edgeValue_pair A z i k hfaceik hik]
  simpa only [CharTwo.neg_eq] using (eq_neg_iff_add_eq_zero.mpr hzt)

noncomputable def cocycleOfClosed (z : Edge A → ZMod 2)
    (hz : edgeCoboundary A z = 0) : A.ModTwoEdgeCocycle where
  value := edgeValue A z
  diagonal := edgeValue_self A z
  compose := fun _ hs _ hi _ hj _ hk => edgeValue_compose A z hz hs hi hj hk

theorem mem_range_vertexCoboundary_of_coboundary (z : Edge A → ZMod 2)
    (hz : edgeCoboundary A z = 0) (hc : (cocycleOfClosed A z hz).IsCoboundary) :
    z ∈ LinearMap.range (vertexCoboundary A) := by
  classical
  obtain ⟨a, ha⟩ := hc
  refine ⟨a, funext fun e => ?_⟩
  obtain ⟨i, j, hij, he⟩ := Finset.card_eq_two.mp e.property.2
  have hi : i ∈ e.val := by rw [he]; simp
  have hj : j ∈ e.val := by rw [he]; simp
  have hface : {i, j} ∈ A.faces := he ▸ e.property.1
  have hvalue := ha e.val e.property.1 i hi j hj
  change edgeValue A z i j = a i + a j at hvalue
  rw [edgeValue_pair A z i j hface hij] at hvalue
  have heq : e = pairEdge A i j hface hij := Subtype.ext he
  rw [heq, vertexCoboundary_pair]
  exact hvalue.symm

omit [Fintype ι] in

theorem boundary1_edge (e : Edge A) :
    (vertexCoboundary A).dualMap (LinearMap.proj e) =
      ∑ i ∈ e.val, (LinearMap.proj i : Module.Dual (ZMod 2) (ι → ZMod 2)) := by
  ext a
  simp [vertexCoboundary_apply]

theorem boundary2_triangle (t : Triangle A) :
    (edgeCoboundary A).dualMap (LinearMap.proj t) =
      ∑ e ∈ triangleEdges A t,
        (LinearMap.proj e : Module.Dual (ZMod 2) (Edge A → ZMod 2)) := by
  ext z
  simp [edgeCoboundary_apply]

end PreAbstractSimplicialComplex.ModTwoCochains
