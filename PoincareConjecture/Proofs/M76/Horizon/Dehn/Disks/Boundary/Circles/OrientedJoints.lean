import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.LocalJointMaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Orientation.CofaceSideTransport

set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex
open AbstractSimplicialComplex PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)



theorem exists_oriented_boundary_joint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] (A : SimplicialComplex ℝ E) [Fintype A.faces]
    (hbound : ∀ t ∈ A.faces, t.card ≤ 3)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (number : E → ℕ) (sign : Finset E → ZMod 2)
    (hcancel : ∀ t ∈ A.faces, t.card = 3 → ∀ u ∈ A.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    {a b : E} (hab : a ≠ b) (hs : ({a, b} : Finset E) ∈ A.faces) :
    ∃ (t : Bool → Finset E)
      (G : signedTubeSheet 0 ≃ₜ (A.barycentricDualBlock {a, b}).space)
      (r : ∀ side, signedTubeRadius 0 side ≃ₜ
        segment ℝ (({a, b} : Finset E).centroid ℝ id) ((t side).centroid ℝ id)),
      (∀ side, t side ∈ A.faces ∧ (t side).card = 3 ∧ ({a, b} : Finset E) ⊆ t side) ∧
      t false ≠ t true ∧
      (∀ u ∈ A.faces, u.card = 3 → ({a, b} : Finset E) ⊆ u → u = t false ∨ u = t true) ∧
      (∀ side, sign (t side) + orderedCofaceParity number (t side) a b = if side then 1 else 0) ∧
      G.IsFinitePL ∧ (∀ side, (r side).IsFinitePL) ∧
      (∀ side (x : signedTubeRadius 0 side),
        (G ⟨x, by cases side; exact Or.inl x.property; exact Or.inr x.property⟩ : E) = r side x) ∧
      (∀ side (x : signedTubeSheet 0),
        (x : P2) ∈ signedTubeRadius 0 side ↔ (G x : E) ∈
          segment ℝ (({a, b} : Finset E).centroid ℝ id) ((t side).centroid ℝ id)) ∧
      (∀ side (x : signedTubeRadius 0 side),
        (r side x : E) = ({a, b} : Finset E).centroid ℝ id ↔ (x : P2) = (0, 0)) ∧
      (∀ side (x : signedTubeRadius 0 side),
        (r side x : E) = (t side).centroid ℝ id ↔ (x : P2) = signedTubeCorner 0 side) ∧
      (G ⟨(0, 0), Or.inl (left_mem_segment ℝ _ _)⟩ : E) = ({a, b} : Finset E).centroid ℝ id := by
  classical
  obtain ⟨t, ht, htn, htex, _, hne, hd, hU, hI⟩ :=
    exists_boundary_circle_joint A hbound hcofaces hs (Finset.card_pair hab)
  let q := fun side => sign (t side) + orderedCofaceParity number (t side) a b
  have hsum : q false + q true = 1 := orderedCofaceParity_cancellation
    number (t false) (t true) a b (sign (t false)) (sign (t true))
      (hcancel _ (ht false).1 (ht false).2.1 _ (ht true).1 (ht true).2.1 htn
        {a, b} (Finset.card_pair hab) (ht false).2.2 (ht true).2.2)
  have hq : q false = 0 ∨ q false = 1 := by
    generalize q false = v
    fin_cases v
    · exact Or.inl rfl
    · exact Or.inr rfl
  let t' := fun side => if q false = 0 then t side else t (!side)
  have ht' (side : Bool) : t' side ∈ A.faces ∧ (t' side).card = 3 ∧
      ({a, b} : Finset E) ⊆ t' side := by
    dsimp only [t']
    split_ifs <;> exact ht _
  have htn' : t' false ≠ t' true := by
    by_cases hq0 : q false = 0
    · simpa only [t', if_pos hq0] using htn
    · simpa only [t', if_neg hq0, Bool.not_false, Bool.not_true] using htn.symm
  have htex' (u : Finset E) (hu : u ∈ A.faces) (huc : u.card = 3)
      (hsu : ({a, b} : Finset E) ⊆ u) : u = t' false ∨ u = t' true := by
    by_cases hq0 : q false = 0
    · simpa only [t', if_pos hq0] using htex u hu huc hsu
    · simpa only [t', if_neg hq0, Bool.not_false, Bool.not_true] using (htex u hu huc hsu).symm
  have hlabels (side : Bool) :
      sign (t' side) + orderedCofaceParity number (t' side) a b = if side then 1 else 0 := by
    rcases hq with hq0 | hq1
    · have hqt : q true = 1 := by simpa only [hq0, zero_add] using hsum
      cases side
      · simpa only [t', if_pos hq0, Bool.false_eq_true, ↓reduceIte] using hq0
      · simpa only [t', if_pos hq0, ↓reduceIte] using hqt
    · have hq0 : q false ≠ 0 := by rw [hq1]; exact one_ne_zero
      have hqt : q true = 0 := by
        have h : (1 : ZMod 2) + q true = 1 + 0 := by simpa only [hq1, add_zero] using hsum
        exact add_left_cancel h
      cases side
      · simpa only [t', if_neg hq0, Bool.not_false, Bool.false_eq_true, ↓reduceIte] using hqt
      · simpa only [t', if_neg hq0, Bool.not_true, ↓reduceIte] using hq1
  have hne' (side : Bool) : ({a, b} : Finset E).centroid ℝ id ≠ (t' side).centroid ℝ id := by
    dsimp only [t']
    split_ifs <;> exact hne _
  have hd' (side : Bool) : IsFinitePLBallPair ℝ
      (segment ℝ (({a, b} : Finset E).centroid ℝ id) ((t' side).centroid ℝ id))
      {({a, b} : Finset E).centroid ℝ id, (t' side).centroid ℝ id} := by
    dsimp only [t']
    split_ifs <;> exact hd _
  have hU' : segment ℝ (({a, b} : Finset E).centroid ℝ id) ((t' false).centroid ℝ id) ∪
      segment ℝ (({a, b} : Finset E).centroid ℝ id) ((t' true).centroid ℝ id) =
      (A.barycentricDualBlock {a, b}).space := by
    by_cases hq0 : q false = 0
    · simpa only [t', if_pos hq0] using hU.symm
    · simpa only [t', if_neg hq0, Bool.not_false, Bool.not_true, union_comm] using hU.symm
  have hI' : segment ℝ (({a, b} : Finset E).centroid ℝ id) ((t' false).centroid ℝ id) ∩
      segment ℝ (({a, b} : Finset E).centroid ℝ id) ((t' true).centroid ℝ id) =
      {({a, b} : Finset E).centroid ℝ id} := by
    by_cases hq0 : q false = 0
    · simpa only [t', if_pos hq0] using hI
    · simpa only [t', if_neg hq0, Bool.not_false, Bool.not_true, inter_comm] using hI
  obtain ⟨G, r, hG, hr, hGr, hGmem, hrm, hrc, hGm⟩ := exists_boundary_joint_map
    (A.barycentricDualBlock {a, b}).space (({a, b} : Finset E).centroid ℝ id)
    (fun side => (t' side).centroid ℝ id) hne' hd' hU' hI'
  exact ⟨t', G, r, ht', htn', htex', hlabels, hG, hr, hGr, hGmem, hrm, hrc, hGm⟩

end PoincareConjecture.M76.Dehn
