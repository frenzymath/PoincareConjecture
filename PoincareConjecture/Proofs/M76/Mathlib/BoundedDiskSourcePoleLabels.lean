import PoincareConjecture.Proofs.M76.Mathlib.PlanarCircleSideLabels
import PoincareConjecture.Proofs.M76.Mathlib.SourcePoleRegionAttachments












set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem exists_common_source_pole_equator_labels
    {F S g d : Set E} (A : E →ₗ[ℝ] ℝ) (hA : A ≠ 0)
    (hdim : Module.finrank ℝ E = 3)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (S ∩ {x | A x = 0}))
    (hdplane : d ⊆ {x | A x = 0})
    (arc : Bool × Bool → Set E) (p : Bool → E) (hp : p false ≠ p true)
    (hArc : ∀ i, IsFinitePLBallPair ℝ (arc i) {p false, p true})
    (hArcInter : Pairwise (fun i j => arc i ∩ arc j = {p false, p true}))
    (hequator : arc (false, false) ∪ arc (false, true) = F ∩ {x | A x = 0})
    (hlink : ∀ i : Bool, arc (true, i) =
      (F ∩ S) ∩ {x | if i then A x ≤ 0 else 0 ≤ A x})
    (ψ : Bool → (ℝ × ℝ) → E)
    (hinj : ∀ j, Function.Injective (ψ j)) (hψzero : ∀ j, ψ j 0 = p j)
    (r : Bool → ℝ) (hr : ∀ j, 0 < r j)
    (hminus : ∀ j, SourcePoleQuadrantData (ψ j) F S g (p j) (p (!j)) A (r j) (-r j))
    (hplus : ∀ j, SourcePoleQuadrantData (ψ j) F S g (p j) (p (!j)) A (r j) (r j))
    (δ : Bool → ℝ) (hδ : ∀ j, 0 < δ j)
    (hside : ∀ j z, |z| ≤ δ j → (ψ j (0, z) ∈ d ↔ 0 ≤ z)) :
    ∃ i : Bool,
      arc (false, i) \ {p false, p true} ⊆ d ∧
      arc (false, !i) \ {p false, p true} ⊆ dᶜ ∧
      ∀ j : Bool,
        ψ j '' ({0} ×ˢ uIcc 0 (r j)) ⊆ arc (false, i) ∧
        ψ j '' ({0} ×ˢ uIcc 0 (-r j)) ⊆ arc (false, !i) := by
  let positive : Bool → Set E := fun j => ψ j '' ({0} ×ˢ uIcc 0 (r j))
  let negative : Bool → Set E := fun j => ψ j '' ({0} ×ˢ uIcc 0 (-r j))
  have hfalse (i : Bool) : arc (false, i) ⊆ F ∩ {x | A x = 0} := by
    cases i
    · exact subset_union_left.trans hequator.subset
    · exact subset_union_right.trans hequator.subset
  have hcontact (i : Bool) :
      arc (false, i) ∩ (S ∩ {x | A x = 0}) ⊆ {p false, p true} := by
    intro x hx
    have hxF := hfalse i hx.1
    have hxlink : x ∈ arc (true, false) :=
      (hlink false).symm.subset ⟨⟨hxF.1, hx.2.1⟩, hxF.2.ge⟩
    exact (hArcInter (show (false, i) ≠ (true, false) by
      intro h
      cases h)).subset ⟨hx.1, hxlink⟩
  have hlabels (j : Bool) :
      ∃ i : Bool, positive j ⊆ arc (false, i) ∧ negative j ⊆ arc (false, !i) := by
    have hmarks : ({p j, p (!j)} : Set E) = {p false, p true} := by
      cases j
      · rfl
      · exact pair_comm _ _
    have hArcj (i : Bool × Bool) : IsFinitePLBallPair ℝ (arc i) {p j, p (!j)} := by
      rw [hmarks]
      exact hArc i
    have hArcInterj : Pairwise (fun i k => arc i ∩ arc k = {p j, p (!j)}) := by
      simpa only [hmarks] using hArcInter
    have hpj : p j ≠ p (!j) := by
      cases j
      · exact hp
      · exact hp.symm
    obtain ⟨i, hn, hpos⟩ := exists_source_pole_equator_labels (hinj j) (hψzero j)
      (hr j) (hminus j) (hplus j) arc hArcj hpj hArcInterj hequator
    exact ⟨!i, hpos, by simpa only [Bool.not_not] using hn⟩
  let η : Bool → ℝ := fun j => min (δ j) (r j) / 2
  have hη (j : Bool) : 0 < η j := half_pos (lt_min (hδ j) (hr j))
  have hηδ (j : Bool) : η j ≤ δ j :=
    (half_lt_self (lt_min (hδ j) (hr j))).le.trans (min_le_left _ _)
  have hηr (j : Bool) : η j ≤ r j :=
    (half_lt_self (lt_min (hδ j) (hr j))).le.trans (min_le_right _ _)
  have hposmem (j : Bool) : ψ j (0, η j) ∈ positive j := by
    refine ⟨(0, η j), ⟨rfl, ?_⟩, rfl⟩
    rw [uIcc_of_le (hr j).le]
    exact ⟨(hη j).le, hηr j⟩
  have hnegmem (j : Bool) : ψ j (0, -η j) ∈ negative j := by
    refine ⟨(0, -η j), ⟨rfl, ?_⟩, rfl⟩
    rw [uIcc_of_ge (neg_nonpos.mpr (hr j).le)]
    exact ⟨neg_le_neg (hηr j), neg_nonpos.mpr (hη j).le⟩
  have hnonmark (j : Bool) (z : ℝ) (hz : z ≠ 0)
      (hmem : ψ j (0, z) ∈ positive j ∨ ψ j (0, z) ∈ negative j) :
      ψ j (0, z) ∉ ({p false, p true} : Set E) := by
    have hself : ψ j (0, z) ≠ p j := by
      intro heq
      have hzero : (0, z) = (0 : ℝ × ℝ) := (hinj j) (heq.trans (hψzero j).symm)
      exact hz (congrArg Prod.snd hzero)
    have hother : ψ j (0, z) ≠ p (!j) := by
      intro heq
      rcases hmem with hm | hm
      · exact (hplus j).vertical_other_notMem (heq ▸ hm)
      · exact (hminus j).vertical_other_notMem (heq ▸ hm)
    cases j
    · exact fun hm => hm.elim hself hother
    · exact fun hm => hm.elim hother hself
  have hpositive (j : Bool) :
      ∃ x ∈ positive j, x ∉ ({p false, p true} : Set E) ∧ x ∈ d := by
    refine ⟨ψ j (0, η j), hposmem j,
      hnonmark j (η j) (hη j).ne' (Or.inl (hposmem j)), ?_⟩
    exact (hside j (η j) (by simpa only [abs_of_pos (hη j)] using hηδ j)).mpr (hη j).le
  have hnegative (j : Bool) :
      ∃ x ∈ negative j, x ∉ ({p false, p true} : Set E) ∧ x ∉ d := by
    refine ⟨ψ j (0, -η j), hnegmem j,
      hnonmark j (-η j) (neg_ne_zero.mpr (hη j).ne') (Or.inr (hnegmem j)), ?_⟩
    intro hxd
    have hnonneg := (hside j (-η j)
      (by simpa only [abs_neg, abs_of_pos (hη j)] using hηδ j)).mp hxd
    linarith [hη j]
  exact hd.exists_common_planar_circle_side_labels A.toAffineMap hA hdim hdplane
    (fun i => arc (false, i)) (fun i => hArc (false, i))
    (fun i => (hfalse i).trans inter_subset_right) hcontact positive negative
    hlabels hpositive hnegative

end Geometry
