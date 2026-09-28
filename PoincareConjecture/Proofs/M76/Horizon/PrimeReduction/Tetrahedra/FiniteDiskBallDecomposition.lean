import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.BallPartitionRefinement

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_finset_proper_disk_ball_decomposition
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S Q : Set E}
    (hS : IsFinitePLBallPair V3 S Q) (D q : ι → Set E)
    (hD : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (D i) (q i))
    (hsub : ∀ i, D i ⊆ S) (hrim : ∀ i, D i ∩ Q = q i)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j)) (s : Finset ι) :
    ∃ κ : Type, Finite κ ∧ ∃ B R : κ → Set E,
      Nat.card κ = s.card + 1 ∧
      (∀ k, IsFinitePLBallPair V3 (B k) (R k)) ∧
      (∀ k, R k = B k ∩ (Q ∪ ⋃ i ∈ s, D i)) ∧
      (⋃ k, B k) = S ∧
      Pairwise (fun k l => B k ∩ B l ⊆ ⋃ i ∈ s, D i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Unit,inferInstance,fun _ => S,fun _ => Q,by simp,fun _ => hS,?_,?_,?_⟩
    · intro _
      simp only [Finset.notMem_empty,iUnion_of_empty,iUnion_empty,union_empty]
      exact (inter_eq_right.mpr hS.1).symm
    · exact iUnion_const S
    · intro k l hkl
      exact (hkl (Subsingleton.elim _ _)).elim
  | @insert i s his ih =>
    obtain ⟨κ,hκ,B,R,hcard,hB,hR,hcover,hinter⟩ := ih
    let : Finite κ := hκ
    have hWT : Disjoint (D i) (⋃ j ∈ s, D j) := by
      apply disjoint_left.mpr
      intro x hxi hx
      obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hx
      have hij : i ≠ j := fun he => his (he.symm ▸ hj)
      exact disjoint_left.mp (hdis hij) hxi hxj
    obtain ⟨κ',hκ',B',R',hcard',hB',hR',hcover',hinter'⟩ :=
      exists_proper_disk_ball_partition_refinement B R hB hR hcover hinter
        (hD i) (hsub i) (hrim i) hWT
    have hcuts : (⋃ j ∈ insert i s, D j) = (⋃ j ∈ s, D j) ∪ D i := by
      simp only [Finset.mem_insert,iUnion_iUnion_eq_or_left]
      exact union_comm _ _
    refine ⟨κ',hκ',B',R',?_,hB',?_,hcover',?_⟩
    · rw [hcard',hcard,Finset.card_insert_of_notMem his]
    · intro k
      simpa only [hcuts] using hR' k
    · simpa only [hcuts] using hinter'

theorem exists_finite_proper_disk_ball_decomposition
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι] {S Q : Set E}
    (hS : IsFinitePLBallPair V3 S Q) (D q : ι → Set E)
    (hD : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (D i) (q i))
    (hsub : ∀ i, D i ⊆ S) (hrim : ∀ i, D i ∩ Q = q i)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j)) :
    ∃ κ : Type, Finite κ ∧ ∃ B R : κ → Set E,
      Nat.card κ = Nat.card ι + 1 ∧
      (∀ k, IsFinitePLBallPair V3 (B k) (R k)) ∧
      (∀ k, R k = B k ∩ (Q ∪ ⋃ i, D i)) ∧
      (⋃ k, B k) = S ∧
      Pairwise (fun k l => B k ∩ B l ⊆ ⋃ i, D i) := by
  classical
  let := Fintype.ofFinite ι
  simpa only [Finset.mem_univ,iUnion_true,Finset.card_univ,Nat.card_eq_fintype_card] using
    exists_finset_proper_disk_ball_decomposition hS D q hD hsub hrim hdis Finset.univ

end PoincareConjecture.M76
