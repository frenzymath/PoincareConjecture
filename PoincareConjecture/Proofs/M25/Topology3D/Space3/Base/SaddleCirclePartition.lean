import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic










set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

private theorem connected_subset_one_closed_piece
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (C : Fin n → Set X)
    (hclosed : ∀ i, IsClosed (C i))
    (hdis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    {S : Set X} (hS : IsConnected S)
    (hcover : S ⊆ ⋃ i, C i) :
    ∃ i, S ⊆ C i := by
  classical
  obtain ⟨x, hx⟩ := hS.nonempty
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
  let O : Set X := ⋃ j : {j : Fin n // j ≠ i}, C j.1
  have hO : IsClosed O :=
    isClosed_iUnion_of_finite fun j => hclosed j.1
  have hd : Disjoint (C i) O := by
    apply Set.disjoint_left.mpr
    intro y hyi hyo
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hyo
    exact Set.disjoint_left.mp (hdis i j.1 (Ne.symm j.2)) hyi hyj
  have htwo : S ⊆ C i ∪ O := by
    intro y hy
    obtain ⟨j, hyj⟩ := mem_iUnion.mp (hcover hy)
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hyj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩)
  have hempty : S ∩ (C i ∩ O) = ∅ := by
    rw [Set.disjoint_iff_inter_eq_empty.mp hd, inter_empty]
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hS.isPreconnected)
      (C i) O (hclosed i) hO htwo hempty with hi | ho
  · exact ⟨i, hi⟩
  · exact False.elim (Set.disjoint_left.mp hd hxi (ho hx))

private theorem finite_connected_partition_equiv
    {X : Type*} [TopologicalSpace X] {n m : ℕ}
    (A : Fin n → Set X) (B : Fin m → Set X)
    (hAc : ∀ i, IsConnected (A i)) (hBc : ∀ j, IsConnected (B j))
    (hAcl : ∀ i, IsClosed (A i)) (hBcl : ∀ j, IsClosed (B j))
    (hAd : ∀ i j, i ≠ j → Disjoint (A i) (A j))
    (hBd : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hcover : (⋃ i, A i) = ⋃ j, B j) :
    ∃ e : Fin n ≃ Fin m, ∀ i, A i = B (e i) := by
  classical
  have hforward : ∀ i, ∃ j, A i ⊆ B j := by
    intro i
    apply connected_subset_one_closed_piece B hBcl hBd (hAc i)
    intro x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, hx⟩
  have hbackward : ∀ j, ∃ i, B j ⊆ A i := by
    intro j
    apply connected_subset_one_closed_piece A hAcl hAd (hBc j)
    intro x hx
    rw [hcover]
    exact mem_iUnion.mpr ⟨j, hx⟩
  choose a ha using hforward
  choose b hb using hbackward
  have hba : ∀ i, b (a i) = i := by
    intro i
    obtain ⟨x, hx⟩ := (hAc i).nonempty
    by_contra hne
    exact Set.disjoint_left.mp (hAd (b (a i)) i hne)
      (hb (a i) (ha i hx)) hx
  have hab : ∀ j, a (b j) = j := by
    intro j
    obtain ⟨x, hx⟩ := (hBc j).nonempty
    by_contra hne
    exact Set.disjoint_left.mp (hBd (a (b j)) j hne)
      (ha (b j) (hb j hx)) hx
  let e : Fin n ≃ Fin m :=
    { toFun := a
      invFun := b
      left_inv := hba
      right_inv := hab }
  refine ⟨e, fun i => subset_antisymm (ha i) ?_⟩
  intro x hx
  have hx' := hb (a i) hx
  simpa only [hba i] using hx'



theorem exists_two_circles_of_ambient_partition
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (n : ℕ) (q : Fin n → UnitCircle → UnitTwoSphere)
    (hq : ∀ i, ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Injective (q i) ∧
      ∀ theta, Injective (mfderiv (𝓡 1) (𝓡 2) (q i) theta))
    (hdisjoint : ∀ i k, i ≠ k → Disjoint (range (q i)) (range (q k)))
    (K : Fin 2 → Set E3) (hKcompact : ∀ b, IsCompact (K b))
    (hKconnected : ∀ b, IsConnected (K b))
    (hKdis : ∀ b k, b ≠ k → Disjoint (K b) (K k))
    (hcover : (⋃ i, range (fun theta => psi (q i theta, 0))) = ⋃ b, K b) :
    ∃ q2 : Fin 2 → UnitCircle → UnitTwoSphere,
      (∀ b, ContMDiff (𝓡 1) (𝓡 2) ∞ (q2 b) ∧ Injective (q2 b) ∧
        ∀ theta, Injective (mfderiv (𝓡 1) (𝓡 2) (q2 b) theta)) ∧
      (∀ b k, b ≠ k → Disjoint (range (q2 b)) (range (q2 k))) ∧
      (⋃ b, range (q2 b)) = ⋃ i, range (q i) := by
  classical
  let j : UnitTwoSphere → E3 := fun p => psi (p, 0)
  have hj : Continuous j := (collar_central_contMDiff psi hpsi).continuous
  have hji : Injective j := by
    intro p r hpr
    exact congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpr)
  let Q : Fin n → Set E3 := fun i => range (j ∘ q i)
  have hQc (i : Fin n) : IsConnected (Q i) := by
    have hdim : 1 < Module.rank ℝ E2 :=
      Module.one_lt_rank_of_one_lt_finrank (by simp [E2])
    let : ConnectedSpace UnitCircle := Subtype.connectedSpace
      (isConnected_sphere hdim (0 : E2) (by norm_num : (0 : ℝ) ≤ 1))
    exact isConnected_range (hj.comp (hq i).1.continuous)
  have hQcl (i : Fin n) : IsClosed (Q i) :=
    (isCompact_range (hj.comp (hq i).1.continuous)).isClosed
  have hQdis (i k : Fin n) (hik : i ≠ k) : Disjoint (Q i) (Q k) := by
    apply disjoint_left.mpr
    rintro x ⟨theta, rfl⟩ ⟨phi, heq⟩
    exact disjoint_left.mp (hdisjoint i k hik)
      ⟨theta, rfl⟩ ⟨phi, hji heq⟩
  obtain ⟨e, _he⟩ := finite_connected_partition_equiv Q K hQc hKconnected hQcl
    (fun b => (hKcompact b).isClosed) hQdis hKdis hcover
  let q2 : Fin 2 → UnitCircle → UnitTwoSphere := fun b => q (e.symm b)
  refine ⟨q2, fun b => hq (e.symm b), ?_, ?_⟩
  · intro b k hbk
    exact hdisjoint (e.symm b) (e.symm k) (fun h => hbk (e.symm.injective h))
  · ext p
    constructor
    · intro hp
      obtain ⟨b, hb⟩ := mem_iUnion.mp hp
      exact mem_iUnion.mpr ⟨e.symm b, hb⟩
    · intro hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      refine mem_iUnion.mpr ⟨e i, ?_⟩
      simpa only [q2, e.symm_apply_apply] using hi

end PoincareConjecture.M25.Topology3D
