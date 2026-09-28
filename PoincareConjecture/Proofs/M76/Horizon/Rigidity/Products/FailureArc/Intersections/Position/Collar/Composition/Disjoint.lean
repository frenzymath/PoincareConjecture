import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalPLMotionComposition



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_disjoint_original_motions_composition
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (s : Finset κ) (U C : κ → Set X) (G : κ → X ≃ₜ X)
    (hdis : (s : Set κ).PairwiseDisjoint U)
    (hC : ∀ i ∈ s, IsCompact (C i)) (hCU : ∀ i ∈ s, C i ⊆ U i)
    (hfix : ∀ i ∈ s, EqOn (G i) id (C i)ᶜ)
    (hPL : ∀ k ∈ s, ∀ i j, (e i).symm.trans ((G k).toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hInv : ∀ k ∈ s, ∀ i j, (e i).symm.trans ((G k).symm.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3) :
    ∃ (F : X ≃ₜ X) (K : Set X),
      IsCompact K ∧ K ⊆ ⋃ i ∈ s, C i ∧ EqOn F id Kᶜ ∧
      (∀ i ∈ s, EqOn F (G i) (U i)) ∧
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      ∀ R : Set X, (∀ i ∈ s, (G i) ⁻¹' R = R) → F ⁻¹' R = R := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hid : ∀ i j, (e i).symm.trans
        ((Homeomorph.refl X).toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3 := by
      intro i j
      change (e i).symm.trans ((OpenPartialHomeomorph.refl X).trans (e j)) ∈ _
      simpa only [OpenPartialHomeomorph.refl_trans] using he i j
    exact ⟨Homeomorph.refl X, ∅, isCompact_empty, empty_subset _,
      fun _ _ => rfl, by simp, hid, hid, fun _ _ => rfl⟩
  | @insert k s hks ih =>
    have hs : (s : Set κ) ⊆ (↑(insert k s) : Set κ) := by simp
    obtain ⟨F, K, hK, hKC, hFfix, hFG, hFPL, hFinv, hmark⟩ :=
      ih (fun i hi j hj hij => hdis (hs hi) (hs hj) hij)
        (fun i hi => hC i (Finset.mem_insert_of_mem hi))
        (fun i hi => hCU i (Finset.mem_insert_of_mem hi))
        (fun i hi => hfix i (Finset.mem_insert_of_mem hi))
        (fun i hi => hPL i (Finset.mem_insert_of_mem hi))
        (fun i hi => hInv i (Finset.mem_insert_of_mem hi))
    have hk : k ∈ insert k s := Finset.mem_insert_self _ _
    have hUk (x : X) (hx : x ∈ U k) : F x = x := by
      apply hFfix
      intro hxK
      obtain ⟨j, hj, hxC⟩ := mem_iUnion₂.mp (hKC hxK)
      exact disjoint_left.mp (hdis hk (Finset.mem_insert_of_mem hj)
        (fun h => hks (h ▸ hj))) hx (hCU j (Finset.mem_insert_of_mem hj) hxC)
    have hGU (i : κ) (hi : i ∈ insert k s) : MapsTo (G i) (U i) (U i) := by
      intro x hx
      by_contra hn
      have hnot : G i x ∉ C i := fun h => hn (hCU i hi h)
      have heq : G i x = x := (G i).injective (hfix i hi hnot)
      exact hn (heq.symm ▸ hx)
    refine ⟨F.trans (G k), K ∪ C k, hK.union (hC k hk), ?_, ?_, ?_,
      original_PL_motion_trans e hcover F (G k) hFPL (hPL k hk),
      original_PL_motion_trans e hcover (G k).symm F.symm (hInv k hk) hFinv, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp (hKC hx)
        exact mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem hi, hx⟩
      · exact mem_iUnion₂.mpr ⟨k, hk, hx⟩
    · intro x hx
      change G k (F x) = x
      rw [hFfix (fun h => hx (Or.inl h))]
      exact hfix k hk (fun h => hx (Or.inr h))
    · intro i hi x hx
      change G k (F x) = G i x
      rcases Finset.mem_insert.mp hi with rfl | hi
      · rw [hUk x hx]
      · rw [hFG i hi hx]
        apply hfix k hk
        intro h
        exact disjoint_left.mp (hdis (Finset.mem_insert_of_mem hi) hk
          (fun h => hks (h ▸ hi))) (hGU i (Finset.mem_insert_of_mem hi) hx) (hCU k hk h)
    · intro R hR
      change F ⁻¹' ((G k) ⁻¹' R) = R
      rw [hR k hk]
      exact hmark R (fun i hi => hR i (Finset.mem_insert_of_mem hi))

end PoincareConjecture.M76
