import PoincareConjecture.Proofs.M76.Mathlib.PolygonCutArcIncidence
import PoincareConjecture.Proofs.M76.Mathlib.ThinPrismContactConfinement
import PoincareConjecture.Proofs.M76.Mathlib.FinitePositiveHeightGap











set_option autoImplicit false

open Set CoordinateHalfBoxes

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}






theorem exists_thin_original_cutArc_contacts
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (t : Fin (n + 3) → ℝ)
    (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1)
    (R : Fin (n + 3) → ℝ) (hR : ∀ i, 0 < R i)
    (F : Fin (n + 3) → ((ℝ × ℝ) × ℝ) → E)
    (hF : ∀ i, ContinuousOn (F i) (box (R i)))
    (hcore : ∀ i, F i '' (({0} ×ˢ Icc (-R i) (R i)) ×ˢ {0}) = P.cutArc t i)
    (f : Fin (n + 3) → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    (hfzero : ∀ i, f i 0 = P.edgeCut t i) {q ε : ℝ} (hq : 0 < q) (hε : 0 < ε) :
    ∃ r : ℝ, r ∈ Ioo 0 ε ∧ r < q ∧ (∀ i, r < R i) ∧
      ∀ δ : ℝ, δ ≤ r →
        (∀ i, (F i '' ((Icc (-δ) δ ×ˢ Icc (-R i) (R i)) ×ˢ Icc (-δ) δ)) ∩
          (F (finRotate (n + 3) i) ''
            ((Icc (-δ) δ ×ˢ Icc (-R (finRotate (n + 3) i))
              (R (finRotate (n + 3) i))) ×ˢ Icc (-δ) δ)) ⊆
                f (finRotate (n + 3) i) '' interior (box q)) ∧
        ∀ i j, i ≠ j → finRotate (n + 3) i ≠ j → finRotate (n + 3) j ≠ i →
          Disjoint
            (F i '' ((Icc (-δ) δ ×ˢ Icc (-R i) (R i)) ×ˢ Icc (-δ) δ))
            (F j '' ((Icc (-δ) δ ×ˢ Icc (-R j) (R j)) ×ˢ Icc (-δ) δ)) := by
  classical
  let V (i : Fin (n + 3)) : Set E := f i '' interior (box q)
  have hV (i : Fin (n + 3)) : IsOpen (V i) :=
    (f i).toHomeomorph.isOpenMap _ isOpen_interior
  have hmark (i : Fin (n + 3)) : P.edgeCut t i ∈ V i :=
    ⟨0, zero_mem_interior_box hq, hfzero i⟩
  let W (i j : Fin (n + 3)) : Set E := if i = j then univ else
    (if finRotate (n + 3) i = j then V j else ∅) ∪
      (if finRotate (n + 3) j = i then V i else ∅)
  have hW (i j : Fin (n + 3)) : IsOpen (W i j) := by
    dsimp only [W]
    split_ifs
    all_goals first
      | exact isOpen_univ
      | apply IsOpen.union <;> first | exact isOpen_empty | exact hV _
  have hcoreW (i j : Fin (n + 3)) :
      (F i '' (({0} ×ˢ Icc (-R i) (R i)) ×ˢ {0})) ∩
        (F j '' (({0} ×ˢ Icc (-R j) (R j)) ×ˢ {0})) ⊆ W i j := by
    rw [hcore i, hcore j]
    by_cases hij : i = j
    · simp only [W, if_pos hij, subset_univ]
    rw [P.cutArc_inter_of_ne hP hinj t ht hij]
    rintro x ⟨hi | hi, hj | hj⟩
    · exact (hij (P.edgeCut_injective hP hinj t ht (hi.symm.trans hj))).elim
    · have hji : finRotate (n + 3) j = i :=
        (P.edgeCut_injective hP hinj t ht (hi.symm.trans hj)).symm
      simp only [W, if_neg hij, if_pos hji]
      exact Or.inr (hi.symm ▸ hmark i)
    · have hij' : finRotate (n + 3) i = j :=
        P.edgeCut_injective hP hinj t ht (hi.symm.trans hj)
      simp only [W, if_neg hij, if_pos hij']
      exact Or.inl (hj.symm ▸ hmark j)
    · exact (hij ((finRotate (n + 3)).injective
        (P.edgeCut_injective hP hinj t ht (hi.symm.trans hj)))).elim
  have hpairs (i j : Fin (n + 3)) :
      ∃ s : ℝ, s ∈ Ioo 0 ε ∧ s < R i ∧ s < R j ∧
        ∀ δ : ℝ, δ ≤ s →
          (F i '' ((Icc (-δ) δ ×ˢ Icc (-R i) (R i)) ×ˢ Icc (-δ) δ)) ∩
            (F j '' ((Icc (-δ) δ ×ˢ Icc (-R j) (R j)) ×ˢ Icc (-δ) δ)) ⊆ W i j :=
    exists_thin_prism_contact_subset (hR i) (hR j) (hF i) (hF j) (hW i j)
      (hcoreW i j) hε
  choose s hs hsR hsS hcontrol using hpairs
  obtain ⟨r, hr, hsmall⟩ :=
    (Set.toFinite (univ : Set (Fin (n + 3) × Fin (n + 3)))).exists_pos_lt_positive_values
      (fun p => s p.1 p.2) (lt_min hε hq)
  have hrs (i j : Fin (n + 3)) : r < s i j :=
    hsmall (i, j) (mem_univ _) (hs i j).1
  have hrotate (i : Fin (n + 3)) : i ≠ finRotate (n + 3) i := by
    intro h
    exact P.edge_endpoints_ne_of_injective hinj i (congrArg P h)
  have hrotate2 (i : Fin (n + 3)) :
      finRotate (n + 3) (finRotate (n + 3) i) ≠ i := by
    simp only [finRotate_apply, add_assoc]
    intro h
    have htwo : (1 : Fin (n + 3)) + 1 = 0 := add_left_cancel
      (show i + (1 + 1) = i + 0 by simpa only [add_zero] using h)
    have hval := congrArg Fin.val htwo
    change (1 % (n + 3) + 1 % (n + 3)) % (n + 3) = 0 at hval
    rw [Nat.mod_eq_of_lt (by omega : 1 < n + 3)] at hval
    norm_num only [Nat.reduceAdd] at hval
    rw [Nat.mod_eq_of_lt (by omega)] at hval
    omega
  refine ⟨r, ⟨hr.1, hr.2.trans_le (min_le_left _ _)⟩,
    hr.2.trans_le (min_le_right _ _), fun i => (hrs i i).trans (hsR i i), ?_⟩
  intro δ hδ
  constructor
  · intro i
    have h := hcontrol i (finRotate (n + 3) i) δ
      (hδ.trans (hrs i (finRotate (n + 3) i)).le)
    simpa only [W, V, if_neg (hrotate i), if_pos rfl, if_true,
      if_neg (hrotate2 i), union_empty]
      using h
  · intro i j hij hi hj
    have h := hcontrol i j δ (hδ.trans (hrs i j).le)
    have hempty : W i j = ∅ := by simp only [W, if_neg hij, if_neg hi, if_neg hj, union_self]
    rw [hempty] at h
    exact disjoint_iff_inter_eq_empty.mpr (Subset.antisymm h (empty_subset _))

end Polygon
