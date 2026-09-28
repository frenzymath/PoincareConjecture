import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.DiskIncidenceRefinement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Cutting.FiniteArcComponentCount

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "V3" => (Fin 3 → ℝ)

theorem exists_finset_disk_partition_with_whole_incidence
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
      Pairwise (fun k l => B k ∩ B l ⊆ ⋃ i ∈ s, D i) ∧
      ∀ i ∈ s, HasTwoWholeOwners B (D i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Unit,inferInstance,fun _ => S,fun _ => Q,by simp,fun _ => hS,?_,?_,?_,?_⟩
    · intro _
      simp only [Finset.notMem_empty,iUnion_of_empty,iUnion_empty,union_empty]
      exact (inter_eq_right.mpr hS.1).symm
    · exact iUnion_const S
    · intro k l hkl
      exact (hkl (Subsingleton.elim _ _)).elim
    · simp
  | @insert i s his ih =>
    obtain ⟨κ,hκ,B,R,hcard,hB,hR,hcover,hinter,howners⟩ := ih
    let : Finite κ := hκ
    have hWT : Disjoint (D i) (⋃ j ∈ s, D j) := by
      apply disjoint_left.mpr
      intro x hxi hx
      obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hx
      have hij : i ≠ j := fun he => his (he.symm ▸ hj)
      exact disjoint_left.mp (hdis hij) hxi hxj
    obtain ⟨κ',hκ',B',R',hcard',hB',hR',hcover',hinter',hnew,hretain⟩ :=
      exists_proper_disk_partition_with_whole_incidence B R hB hR hcover hinter
        (hD i) (hsub i) (hrim i) hWT
    have hcuts : (⋃ j ∈ insert i s, D j) = (⋃ j ∈ s, D j) ∪ D i := by
      simp only [Finset.mem_insert,iUnion_iUnion_eq_or_left]
      exact union_comm _ _
    refine ⟨κ',hκ',B',R',?_,hB',?_,hcover',?_,?_⟩
    · rw [hcard',hcard,Finset.card_insert_of_notMem his]
    · intro k
      simpa only [hcuts] using hR' k
    · simpa only [hcuts] using hinter'
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hnew
      · exact hretain (D j) (hD j).isConnected
          (hdis (fun he => his (he ▸ hj))) (howners j hj)

theorem exists_finite_disk_partition_with_whole_incidence
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
      Pairwise (fun k l => B k ∩ B l ⊆ ⋃ i, D i) ∧
      (∀ i, HasTwoWholeOwners B (D i)) ∧
      (∀ k x, x ∈ B k \ ⋃ i, D i →
        connectedComponentIn (S \ ⋃ i, D i) x = B k \ ⋃ i, D i) ∧
      (∀ k, closure (B k \ ⋃ i, D i) = B k) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨κ,hκ,B,R,hcard,hB,hR,hcover,hinter,howners⟩ :=
    exists_finset_disk_partition_with_whole_incidence hS D q hD hsub hrim hdis Finset.univ
  let : Finite κ := hκ
  simp only [Finset.mem_univ,iUnion_true,Finset.card_univ] at hcard hR hinter howners
  obtain ⟨_,hcomp,hclosure⟩ := disk_partition_components B R hB hR hcover hinter
  exact ⟨κ,hκ,B,R,by simpa only [Nat.card_eq_fintype_card] using hcard,
    hB,hR,hcover,hinter,(fun i => howners i trivial),hcomp,hclosure⟩

end PoincareConjecture.M76.PrismBelt
