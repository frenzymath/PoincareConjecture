import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Circles.LocalJoints
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondMaps

set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)




theorem exists_boundary_joint_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (J : Set E) (m : E) (a : Bool → E)
    (hne : ∀ b, m ≠ a b)
    (hball : ∀ b, IsFinitePLBallPair ℝ (segment ℝ m (a b)) {m, a b})
    (hunion : segment ℝ m (a false) ∪ segment ℝ m (a true) = J)
    (hinter : segment ℝ m (a false) ∩ segment ℝ m (a true) = {m}) :
    ∃ (G : signedTubeSheet 0 ≃ₜ J)
      (r : ∀ b, signedTubeRadius 0 b ≃ₜ segment ℝ m (a b)),
      G.IsFinitePL ∧ (∀ b, (r b).IsFinitePL) ∧
      (∀ b (x : signedTubeRadius 0 b),
        (G ⟨x, by cases b; exact Or.inl x.property; exact Or.inr x.property⟩ : E) = r b x) ∧
      (∀ b (x : signedTubeSheet 0),
        (x : P2) ∈ signedTubeRadius 0 b ↔ (G x : E) ∈ segment ℝ m (a b)) ∧
      (∀ b (x : signedTubeRadius 0 b), (r b x : E) = m ↔ (x : P2) = (0, 0)) ∧
      (∀ b (x : signedTubeRadius 0 b),
        (r b x : E) = a b ↔ (x : P2) = signedTubeCorner 0 b) ∧
      (G ⟨(0, 0), Or.inl (left_mem_segment ℝ _ _)⟩ : E) = m := by
  classical
  choose r hr hrm hra using fun b =>
    (signedTube_radius_ball 0 b).exists_marked_interval_homeomorph
      (hball b) (signedTube_corner_ne_center 0 b).symm (hne b)
  have hsrc := signedTube_radius_inter 0 false
  have hoverlap (x : signedTubeRadius 0 false) :
      (x : P2) ∈ signedTubeRadius 0 true ↔ (r false x : E) ∈ segment ℝ m (a true) := by
    have hx : (x : P2) ∈ signedTubeRadius 0 true ↔ (x : P2) = (0, 0) := by
      constructor
      · intro h
        exact hsrc.subset ⟨x.property, h⟩
      · intro h
        rw [h]
        exact left_mem_segment ℝ _ _
    have hy : (r false x : E) ∈ segment ℝ m (a true) ↔ (r false x : E) = m := by
      constructor
      · exact fun h => hinter.subset ⟨(r false x).property, h⟩
      · intro h
        rw [h]
        exact left_mem_segment ℝ _ _
    rw [hx, hy, hrm]
  have hagree (x : P2) (hx : x ∈ signedTubeRadius 0 false)
      (hy : x ∈ signedTubeRadius 0 true) : (r false ⟨x, hx⟩ : E) = r true ⟨x, hy⟩ := by
    have hzero : x = (0, 0) := hsrc.subset ⟨hx, hy⟩
    exact ((hrm false ⟨x, hx⟩).mpr hzero).trans ((hrm true ⟨x, hy⟩).mpr hzero).symm
  obtain ⟨H, hH, hHf, hHt⟩ := Homeomorph.exists_union_finitePL
    (r false) (r true) (hr false) (hr true) hoverlap hagree
  let G : signedTubeSheet 0 ≃ₜ J := H.trans (Homeomorph.setCongr hunion)
  have hG : G.IsFinitePL := by
    obtain ⟨g, hg, hval⟩ := hH
    exact ⟨g, hg, hval⟩
  have hkeep (b : Bool) (x : signedTubeRadius 0 b) :
      (G ⟨x, by cases b; exact Or.inl x.property; exact Or.inr x.property⟩ : E) = r b x := by
    cases b
    · exact hHf x
    · exact hHt x
  have hmem (b : Bool) (x : signedTubeSheet 0) :
      (x : P2) ∈ signedTubeRadius 0 b ↔ (G x : E) ∈ segment ℝ m (a b) := by
    have hs (y : P2) (hy : y ∈ signedTubeRadius 0 b) : y ∈ signedTubeSheet 0 := by
      cases b
      · exact Or.inl hy
      · exact Or.inr hy
    have ht (y : E) (hy : y ∈ segment ℝ m (a b)) : y ∈ J := by
      rw [← hunion]
      cases b
      · exact Or.inl hy
      · exact Or.inr hy
    exact G.mem_subset_iff_of_extension (r b) hs ht (fun y => Subtype.ext (hkeep b y)) x
  exact ⟨G, r, hG, hr, hkeep, hmem, hrm, hra,
    (hkeep false ⟨(0, 0), left_mem_segment ℝ _ _⟩).trans
      ((hrm false ⟨(0, 0), left_mem_segment ℝ _ _⟩).mpr rfl)⟩

end PoincareConjecture.M76.Dehn
