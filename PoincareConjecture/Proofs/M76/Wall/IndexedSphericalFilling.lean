import PoincareConjecture.Proofs.M76.Wall.SphericalFrontierFilling
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_indexed_spherical_frontier_filling
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R K P : Set X}
    (hR : PLDomain e R) (hRconn : IsConnected R) (hend : HasOneSimplyConnectedEnd R)
    (hK : PLDomain e K) (hKc : IsCompact K) (hKconn : IsConnected K) (hKR : K ⊆ R)
    (S : κ → Set X) (hS : ∀ i, Nonempty (ChartwisePLSphere e (S i)))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (hSint : ∀ i, S i ⊆ interior R)
    (hfront : frontier K = frontier R ∪ ⋃ i, S i)
    (hrel : frontier ((Subtype.val : R → X) ⁻¹' K) =
      (Subtype.val : R → X) ⁻¹' (⋃ i, S i))
    (hBP : frontier R ⊆ P)
    (hprotect : (Subtype.val : R → X) ⁻¹' P ⊆
      interior ((Subtype.val : R → X) ⁻¹' K)) :
    ∃ (L : Set X) (n : ℕ) (pick : Fin n ↪ κ), 0 < n ∧ n ≤ Nat.card κ ∧
      IsCompact L ∧ IsConnected L ∧ K ⊆ L ∧ L ⊆ R ∧ PLDomain e L ∧
      frontier L = frontier R ∪ ⋃ i, S (pick i) ∧
      frontier ((Subtype.val : R → X) ⁻¹' L) =
        (Subtype.val : R → X) ⁻¹' (⋃ i, S (pick i)) ∧
      IsConnected (((Subtype.val : R → X) ⁻¹' L)ᶜ) ∧
      (Subtype.val : R → X) ⁻¹' P ⊆ interior ((Subtype.val : R → X) ⁻¹' L) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  obtain ⟨L, J, hJ, hLc, hLconn, hKL, hLR, hL, hfrontL, hrelL, hcompl, hkeep⟩ :=
    exists_spherical_frontier_filling hR hRconn hend hK hKc hKconn hKR S hS
      hdisjoint hSint hfront hrel (fun _ hx => hprotect (hBP hx))
  let n := Fintype.card J
  let index : Fin n ≃ J := (Fintype.equivFin J).symm
  let pick : Fin n ↪ κ :=
    ⟨fun i => (index i).val, fun _ _ h => index.injective (Subtype.ext h)⟩
  have hn : 0 < n := by
    obtain ⟨j, hj⟩ := hJ
    exact Fintype.card_pos_iff.mpr ⟨⟨j, hj⟩⟩
  have hbound : n ≤ Nat.card κ := by
    simpa only [n, Fintype.card_coe, Nat.card_eq_fintype_card] using J.card_le_univ
  have hunion : (⋃ i, S (pick i)) = ⋃ j ∈ J, S j := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨(index i).val, (index i).property, hi⟩
    · intro hx
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx
      refine mem_iUnion.mpr ⟨index.symm ⟨j, hj⟩, ?_⟩
      change x ∈ S (index (index.symm ⟨j, hj⟩)).val
      simpa only [index.apply_symm_apply] using hxj
  refine ⟨L, n, pick, hn, hbound, hLc, hLconn, hKL, hLR, hL, ?_, ?_, hcompl,
    hkeep P hprotect⟩
  · rw [hunion]
    exact hfrontL
  · rw [hunion]
    exact hrelL

end PoincareConjecture.M76
