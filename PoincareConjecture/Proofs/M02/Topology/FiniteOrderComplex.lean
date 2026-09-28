import Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Order.Interval.Finset.Nat






set_option autoImplicit false

open scoped BigOperators

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable def finiteOrderComplex (I : Type u) [PartialOrder I] [Fintype I] :
    Geometry.SimplicialComplex Real (I -> Real) := by
  classical
  let A : PreAbstractSimplicialComplex I :=
    { faces := {s | s.Nonempty ∧ ∀ i ∈ s, ∀ j ∈ s, i ≤ j ∨ j ≤ i}
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨hs.1, ?_⟩
        intro t hts ht
        exact ⟨ht, fun i hi j hj => hs.2 i (hts hi) j (hts hj)⟩ }
  refine Geometry.SimplicialComplex.ofAffineIndependent
    (A.map (fun i => Pi.single i (1 : Real))) ?_
  apply (Pi.linearIndependent_single_one I Real).affineIndependent.range.mono
  intro z hz
  simp only [Set.mem_iUnion, Finset.mem_coe] at hz
  obtain ⟨t, ⟨s, hs, rfl⟩, hz⟩ := hz
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨i, rfl⟩

open scoped Classical in
theorem finiteOrderComplex_faces
    (I : Type u) [PartialOrder I] [Fintype I] (t : Finset (I -> Real)) :
    t ∈ (finiteOrderComplex I).faces ↔
      Exists fun s : Finset I => s.Nonempty ∧
        (∀ i ∈ s, ∀ j ∈ s, i ≤ j ∨ j ≤ i) ∧
        t = s.image (fun i => Pi.single i (1 : Real)) := by
  classical
  change (∃ s : Finset I,
    (s.Nonempty ∧ ∀ i ∈ s, ∀ j ∈ s, i ≤ j ∨ j ≤ i) ∧
      s.image (fun i => Pi.single i (1 : Real)) = t) ↔ _
  constructor
  · rintro ⟨s, ⟨hs, hc⟩, hst⟩
    exact ⟨s, hs, hc, hst.symm⟩
  · rintro ⟨s, hs, hc, hts⟩
    exact ⟨s, ⟨hs, hc⟩, hts.symm⟩

theorem finiteOrderComplex_finite
    (I : Type u) [PartialOrder I] [Fintype I] :
    (finiteOrderComplex I).faces.Finite := by
  classical
  refine (Set.finite_range (fun s : Finset I =>
    s.image (fun i => Pi.single i (1 : Real)))).subset ?_
  intro t ht
  obtain ⟨s, hs, hc, rfl⟩ := (finiteOrderComplex_faces I t).mp ht
  exact Set.mem_range_self s

theorem finiteOrderComplex_space
    (I : Type u) [PartialOrder I] [Fintype I] (z : I -> Real) :
    z ∈ (finiteOrderComplex I).space ↔
      (forall i, 0 ≤ z i) ∧ (∑ i, z i) = 1 ∧
        (forall i j, z i ≠ 0 -> z j ≠ 0 -> i ≤ j ∨ j ≤ i) := by
  classical
  constructor
  · intro hz
    obtain ⟨t, ht, hzt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hz
    obtain ⟨s, hs, hc, rfl⟩ := (finiteOrderComplex_faces I t).mp ht
    have hsimplex : z ∈ stdSimplex Real I := by
      apply convexHull_min _ (convex_stdSimplex Real I) hzt
      intro q hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      exact single_mem_stdSimplex Real i
    have hsupport (i : I) (hi : z i ≠ 0) : i ∈ s := by
      by_contra his
      apply hi
      have hzero : Convex Real {q : I -> Real | q i = 0} := by
        intro a ha b hb c d hc hd hcd
        change c * a i + d * b i = 0
        rw [ha, hb]
        simp
      apply convexHull_min _ hzero hzt
      intro q hq
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
      have hij : i ≠ j := fun h => his (h ▸ hj)
      simp only [Set.mem_ofPred_eq, Pi.single_apply, if_neg hij]
    exact ⟨hsimplex.1, hsimplex.2,
      fun i j hi hj => hc i (hsupport i hi) j (hsupport j hj)⟩
  · rintro ⟨hz, hsum, hc⟩
    let s : Finset I := Finset.univ.filter (fun i => z i ≠ 0)
    have hs : s.Nonempty := by
      by_contra hn
      have hz0 : ∀ i, z i = 0 := by
        intro i
        by_contra hi
        exact hn ⟨i, by simp [s, hi]⟩
      simp only [hz0, Finset.sum_const_zero] at hsum
      exact zero_ne_one hsum
    have hsSum : ∑ i ∈ s, z i = 1 := by
      calc
        ∑ i ∈ s, z i = ∑ i, z i := by
          apply Finset.sum_subset (Finset.subset_univ s)
          intro i hi his
          simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using his
        _ = 1 := hsum
    have hvector : ∑ i ∈ s, z i • Pi.single i (1 : Real) = z := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        mul_ite, mul_one, mul_zero]
      by_cases hj : z j = 0
      · simp [s, hj]
      · simp [s, hj]
    apply Geometry.SimplicialComplex.mem_space_iff.mpr
    refine ⟨s.image (fun i => Pi.single i (1 : Real)), ?_, ?_⟩
    · apply (finiteOrderComplex_faces I _).mpr
      refine ⟨s, hs, ?_, rfl⟩
      intro i hi j hj
      exact hc i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    · rw [← hvector, ← Finset.centerMass_eq_of_sum_1 _ _ hsSum]
      apply Finset.centerMass_mem_convexHull
      · exact fun i hi => hz i
      · rw [hsSum]
        exact zero_lt_one
      · intro i hi
        exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

theorem finiteOrderComplex_dimension
    (I : Type u) [PartialOrder I] [Fintype I]
    (r : I -> Nat) (hr : StrictMono r) (a b : Nat)
    (hb : forall i, a ≤ r i ∧ r i ≤ b) :
    ∀ t ∈ (finiteOrderComplex I).faces, t.card ≤ b + 1 - a := by
  classical
  intro t ht
  obtain ⟨s, hs, hc, rfl⟩ := (finiteOrderComplex_faces I t).mp ht
  have hinj : Set.InjOn r (s : Set I) := by
    intro i hi j hj hij
    rcases hc i hi j hj with hle | hle
    · rcases eq_or_lt_of_le hle with heq | hlt
      · exact heq
      · exact ((ne_of_lt (hr hlt)) hij).elim
    · rcases eq_or_lt_of_le hle with heq | hlt
      · exact heq.symm
      · exact ((ne_of_lt (hr hlt)) hij.symm).elim
  calc
    (s.image (fun i => Pi.single i (1 : Real))).card = s.card :=
      Finset.card_image_of_injective s (Pi.linearIndependent_single_one I Real).injective
    _ = (s.image r).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.Icc a b).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_Icc.mpr (hb i)
    _ = b + 1 - a := Nat.card_Icc a b

noncomputable def finiteOrderComplexMap
    (I : Type u) [PartialOrder I] [Fintype I]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace Real E] (c : I -> E) :
    C((finiteOrderComplex I).space, E) where
  toFun z := ∑ i, z.val i • c i
  continuous_toFun := continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_subtype_val).smul continuous_const

theorem finiteOrderComplexMap_apply
    (I : Type u) [PartialOrder I] [Fintype I]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace Real E] (c : I -> E)
    (z : (finiteOrderComplex I).space) :
    finiteOrderComplexMap I c z = ∑ i, z.val i • c i := rfl

end PoincareConjecture.Proofs.M02.Topology
