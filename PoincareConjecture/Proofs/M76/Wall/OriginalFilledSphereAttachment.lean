import PoincareConjecture.Proofs.M76.Wall.OriginalProtectedSphereAttachment
import PoincareConjecture.Proofs.M76.Wall.SelectedEndArc
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ProtectedRelativeFrontier

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_filled_two_sphere_attachment
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R L P F : Set X}
    (hR : PLDomain e R) (hL : PLDomain e L)
    (hLc : IsCompact L) (hLconn : IsConnected L) (hLR : L ⊆ R)
    (hP : IsClosed P) (hPR : P ⊆ R) (hBP : frontier R ⊆ P)
    (hprotect : (Subtype.val : R → X) ⁻¹' P ⊆
      interior ((Subtype.val : R → X) ⁻¹' L))
    (hcompl : IsConnected (((Subtype.val : R → X) ⁻¹' L)ᶜ))
    (hF : IsClosed F) (hFint : F ⊆ interior R)
    (S : Fin 2 → Set X) (hsphere : ∀ i, ChartwisePLSphere e (S i))
    (hSint : ∀ i, S i ⊆ interior R)
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (hFS : ∀ i, Disjoint F (S i))
    (hfront : frontier L = (frontier R ∪ F) ∪ (S 0 ∪ S 1)) :
    ∃ K T : Set X, IsCompact K ∧ IsConnected K ∧ L ⊆ K ∧ K ⊆ R ∧
      K \ L ⊆ interior R \ P ∧ PLDomain e K ∧
      Nonempty (ChartwisePLSphere e T) ∧ T ⊆ interior R ∧ Disjoint F T ∧
      frontier K = frontier R ∪ (F ∪ T) ∧
      frontier ((Subtype.val : R → X) ⁻¹' K) =
        (Subtype.val : R → X) ⁻¹' (F ∪ T) ∧
      (Subtype.val : R → X) ⁻¹' P ⊆ interior ((Subtype.val : R → X) ⁻¹' K) ∧
      ∃ V : Set X, IsOpen V ∧ P ⊆ V ∧ V ∩ K = V ∩ L := by
  have hSfront (i : Fin 2) : S i ⊆ frontier L := by
    intro x hx
    apply hfront.symm.subset
    apply Or.inr
    fin_cases i
    · exact Or.inl hx
    · exact Or.inr hx
  obtain ⟨a, ha⟩ := (hsphere 0).compact_connected.2.nonempty
  obtain ⟨b, hb⟩ := (hsphere 1).compact_connected.2.nonempty
  have hab : a ≠ b := by
    intro heq
    subst b
    exact disjoint_left.mp (hdisjoint (by decide : (0 : Fin 2) ≠ 1)) ha hb
  obtain ⟨q, hq, hqi, hq0, hq1, hqinside, hqcontact⟩ :=
    hL.exists_arc_in_filled_complement hR.closed hP hPR hBP hprotect hcompl
      (hSfront 0 ha) (hSint 0 ha) (hSfront 1 hb) (hSint 1 hb) hab
  have hproper : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∉ L := by
    intro t ht hqt
    rcases (hqcontact t ⟨ht.1.le, ht.2.le⟩).mp hqt with ht0 | ht1
    · exact (ne_of_gt ht.1) ht0
    · exact (ne_of_lt ht.2) ht1
  have hBS (i : Fin 2) : Disjoint (frontier R ∪ F) (S i) := by
    apply disjoint_left.mpr
    rintro x (hxB | hxF) hxS
    · exact hxB.2 (hSint i hxS)
    · exact disjoint_left.mp (hFS i) hxF hxS
  have havoid : Disjoint P (q '' Icc (0 : ℝ) 1) := by
    apply disjoint_left.mpr
    rintro x hxP ⟨t, ht, rfl⟩
    exact (hqinside ht).2 hxP
  have hzero : q 0 ∈ S 0 := by rw [hq0]; exact ha
  have hone : q 1 ∈ S 1 := by rw [hq1]; exact hb
  obtain ⟨K, T, hKc, hKconn, hLK, hadd, hK, hT, hfr, hBT, hnear⟩ :=
    hL.exists_protected_two_sphere_attachment hLc hLconn hq hqi hproper
      S hsphere hSfront hdisjoint hzero hone (isClosed_frontier.union hF) hP
      hfront hBS havoid isOpen_interior (fun _ ht => (hqinside ht).1)
  have hKR : K ⊆ R := by
    intro x hx
    by_cases hxL : x ∈ L
    · exact hLR hxL
    · exact interior_subset (hadd ⟨hx, hxL⟩).1
  have hTint : T ⊆ interior R := by
    intro x hxT
    have hxK : x ∈ K := hK.closed.frontier_subset (hfr.symm.subset (Or.inr hxT))
    by_contra hnot
    have hxB : x ∈ frontier R := by
      rw [hR.closed.frontier_eq]
      exact ⟨hKR hxK, hnot⟩
    exact disjoint_left.mp hBT (Or.inl hxB) hxT
  have hfr' : frontier K = frontier R ∪ (F ∪ T) :=
    hfr.trans (union_assoc _ _ _)
  have hprotect' : (Subtype.val : R → X) ⁻¹' P ⊆
      interior ((Subtype.val : R → X) ⁻¹' K) :=
    hprotect.trans (interior_mono (preimage_mono hLK))
  have hrel : frontier ((Subtype.val : R → X) ⁻¹' K) =
      (Subtype.val : R → X) ⁻¹' (F ∪ T) :=
    protected_relative_frontier_eq_of_frontier hR.closed hK.closed hKR
      (union_subset hFint hTint) (fun _ hx => hprotect' (hBP hx)) hfr'
  exact ⟨K, T, hKc, hKconn, hLK, hKR, hadd, hK, hT, hTint,
    hBT.mono subset_union_right subset_rfl, hfr', hrel, hprotect', hnear⟩

end PoincareConjecture.M76
