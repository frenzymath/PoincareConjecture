import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Faces.Cutting.DiskPartitionRefinement
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Actual finite disk decomposition by disjoint proper arcs

Each original proper arc is cut in its constructed unique disk. The
result has exactly one more disk than arcs; every complete rim is the
intersection with the original rim and the original cutting arcs.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

/-- Cut a selected finite subfamily of actual disjoint proper arcs.
All resulting disks and their whole rims are constructed. -/
theorem exists_finset_proper_arc_disk_decomposition
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S Q : Set E}
    (hS : IsFinitePLBallPair (ℝ × ℝ) S Q)
    (D : ι → Set E) (p q : ι → E)
    (hD : ∀ i, IsFinitePLBallPair ℝ (D i) {p i, q i})
    (hpq : ∀ i, p i ≠ q i) (hsub : ∀ i, D i ⊆ S)
    (hrim : ∀ i, ({p i, q i} : Set E) = D i ∩ Q)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j)) (s : Finset ι) :
    ∃ κ : Type, Finite κ ∧ ∃ B R : κ → Set E,
      Nat.card κ = s.card + 1 ∧
      (∀ k, IsFinitePLBallPair (ℝ × ℝ) (B k) (R k)) ∧
      (∀ k, R k = B k ∩ (Q ∪ ⋃ i ∈ s, D i)) ∧
      (⋃ k, B k) = S ∧
      Pairwise (fun k l => B k ∩ B l ⊆ ⋃ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ => S, fun _ => Q, by simp, fun _ => hS, ?_, ?_, ?_⟩
    · intro _
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, union_empty]
      exact (inter_eq_right.mpr hS.1).symm
    · exact iUnion_const S
    · intro k l hkl
      exact False.elim (hkl (Subsingleton.elim _ _))
  | @insert i s his ih =>
    obtain ⟨κ, hκ, B, R, hcard, hB, hR, hcover, hinter⟩ := ih
    let : Finite κ := hκ
    have hWT : Disjoint (D i) (⋃ j ∈ s, D j) := by
      apply disjoint_left.mpr
      intro x hxi hx
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
      have hij : i ≠ j := fun he => his (he.symm ▸ hj)
      exact disjoint_left.mp (hdis hij) hxi hxj
    obtain ⟨B', R', hB', hR', hcover', hinter'⟩ :=
      exists_proper_arc_disk_partition_refinement B R hB hR hcover hinter
        (hD i) (hpq i) (hsub i) (hrim i) hWT
    have hcuts : (⋃ j ∈ insert i s, D j) = (⋃ j ∈ s, D j) ∪ D i := by
      simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
      exact union_comm _ _
    refine ⟨Option κ, inferInstance, B', R', ?_, hB', ?_, hcover', ?_⟩
    · rw [Finite.card_option, hcard, Finset.card_insert_of_notMem his]
    · intro k
      simpa only [hcuts] using hR' k
    · simpa only [hcuts] using hinter'

/-- A finite family of disjoint proper arcs constructs exactly `n+1`
actual finite PL disks in the original disk, with exact complete rims
and all pairwise intersections contained in the actual arc carrier. -/
theorem exists_finite_proper_arc_disk_decomposition
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι] {S Q : Set E}
    (hS : IsFinitePLBallPair (ℝ × ℝ) S Q)
    (D : ι → Set E) (p q : ι → E)
    (hD : ∀ i, IsFinitePLBallPair ℝ (D i) {p i, q i})
    (hpq : ∀ i, p i ≠ q i) (hsub : ∀ i, D i ⊆ S)
    (hrim : ∀ i, ({p i, q i} : Set E) = D i ∩ Q)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j)) :
    ∃ κ : Type, Finite κ ∧ ∃ B R : κ → Set E,
      Nat.card κ = Nat.card ι + 1 ∧
      (∀ k, IsFinitePLBallPair (ℝ × ℝ) (B k) (R k)) ∧
      (∀ k, R k = B k ∩ (Q ∪ ⋃ i, D i)) ∧
      (⋃ k, B k) = S ∧
      Pairwise (fun k l => B k ∩ B l ⊆ ⋃ i, D i) := by
  classical
  let := Fintype.ofFinite ι
  simpa only [Finset.mem_univ, iUnion_true, Finset.card_univ, Nat.card_eq_fintype_card] using
    exists_finset_proper_arc_disk_decomposition hS D p q hD hpq hsub hrim hdis Finset.univ

end PoincareMT.M76
