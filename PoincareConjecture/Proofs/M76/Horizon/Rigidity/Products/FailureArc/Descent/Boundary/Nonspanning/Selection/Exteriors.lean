import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Exteriors
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Hole
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.StripArmCharts



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1

structure NonspanningStripExteriors (c : Bool → P2 → P2) (D T : Set P2) where
  first : Set P2
  middle : Set P2
  last : Set P2
  s0 : Bool
  s1 : Bool
  first_ball : IsFinitePLBallPair P2 first
    ((first ∩ frontier T) ∪ c false '' arm (farArmParameter (!s0)))
  middle_ball : IsFinitePLBallPair P2 middle
    (((middle ∩ frontier T) ∪ c false '' arm (farArmParameter s0)) ∪
      c true '' arm (farArmParameter s1))
  last_ball : IsFinitePLBallPair P2 last
    ((last ∩ frontier T) ∪ c true '' arm (farArmParameter (!s1)))
  disjoint_first_middle : Disjoint first middle
  disjoint_middle_last : Disjoint middle last
  disjoint_first_last : Disjoint first last
  cover : ((first ∪ middle) ∪ last) ∪ (c false '' source ∪ c true '' source) = T
  strip_first : c false '' source ∩ first = c false '' arm (farArmParameter (!s0))
  strip_middle0 : c false '' source ∩ middle = c false '' arm (farArmParameter s0)
  strip_middle1 : c true '' source ∩ middle = c true '' arm (farArmParameter s1)
  strip_last : c true '' source ∩ last = c true '' arm (farArmParameter (!s1))
  opposite_first : Disjoint first (c true '' source)
  opposite_last : Disjoint last (c false '' source)
  arm_outer : ∀ j b,
    (c j '' arm (farArmParameter b)) ∩ frontier T =
      {c j (0, farArmParameter b), c j (1, farArmParameter b)}
  chain : NonspanningChainGeometry first middle last
    (fun t ↦ c false ((t : ℝ), farArmParameter (!s0)))
    (fun t ↦ c true ((t : ℝ), farArmParameter s1))
    (fun t ↦ c false ((t : ℝ), farArmParameter s0))
    (fun t ↦ c true ((t : ℝ), farArmParameter (!s1)))
  hole : NonspanningChainHole chain D

theorem nonempty_nonspanningStripExteriors
    {D T : Set P2} (hT : IsFinitePLBallPair P2 T (frontier T))
    (hD : IsFinitePLBallPair P2 D (frontier D)) (hDT : D ⊆ interior T)
    (c : Bool → P2 → P2) (hcPL : ∀ j, FinitePiecewiseAffineOn (c j) source)
    (hci : ∀ j, InjOn (c j) source) (hcT : ∀ j, MapsTo (c j) source T)
    (hcQ : ∀ j p, p ∈ source → (c j p ∈ frontier T ↔ p.1 = 0 ∨ p.1 = 1))
    (hdis : Disjoint (c false '' source) (c true '' source))
    (havoid : Disjoint (c false '' source ∪ c true '' source) D) :
    Nonempty (NonspanningStripExteriors c D T) := by
  obtain ⟨A, M, C, s0, s1, hA, hM, hC, hAM, hMC, hAC, hcover,
    h0A, h0M, h1M, h1C, hA1, hC0, E, hE, hDE, _⟩ :=
    exists_nonspanning_strip_exterior_annulus hT c hcPL hci hcT hcQ hdis hD hDT havoid
  have hfar (b : Bool) : farArmParameter b ∈ Icc (-1 : ℝ) 1 := by
    cases b <;> norm_num [farArmParameter]
  obtain ⟨hWA, hane, pA, hpA, hpAval⟩ := exists_embedded_strip_arm_parameter
    (c false) (hcPL false) (hci false) (farArmParameter (!s0)) (hfar (!s0))
  obtain ⟨hWL, hlne, pL, hpL, hpLval⟩ := exists_embedded_strip_arm_parameter
    (c true) (hcPL true) (hci true) (farArmParameter s1) (hfar s1)
  obtain ⟨hWR, _, pR, hpR, hpRval⟩ := exists_embedded_strip_arm_parameter
    (c false) (hcPL false) (hci false) (farArmParameter s0) (hfar s0)
  obtain ⟨hWC, hcne, pC, hpC, hpCval⟩ := exists_embedded_strip_arm_parameter
    (c true) (hcPL true) (hci true) (farArmParameter (!s1)) (hfar (!s1))
  have hLR := hdis.symm.mono (image_mono (arm_far_subset_source s1))
    (image_mono (arm_far_subset_source s0))
  have hchain := nonempty_nonspanningChainGeometry hA hM hC hWA hWL hWR hWC
    subset_union_right subset_union_right (subset_union_right.trans subset_union_left)
    subset_union_right hLR hane hlne hcne pA pL pR pC hpA hpL hpR hpC
    (hpAval 0) (hpAval 1) (hpLval 0) (hpLval 1) (hpRval 0) (hpRval 1)
    (hpCval 0) (hpCval 1)
  have hpAeq := funext hpAval
  have hpLeq := funext hpLval
  have hpReq := funext hpRval
  have hpCeq := funext hpCval
  rw [hpAeq, hpLeq, hpReq, hpCeq] at hchain
  obtain ⟨chain⟩ := hchain
  have hAf (t : I01) : c false ((t : ℝ), farArmParameter (!s0)) ∈ frontier A := by
    rw [hA.frontier_eq_of_finrank_eq rfl]
    exact Or.inr ⟨((t : ℝ), farArmParameter (!s0)), ⟨t.property, rfl⟩, rfl⟩
  have hLf (t : I01) : c true ((t : ℝ), farArmParameter s1) ∈ frontier M := by
    rw [hM.frontier_eq_of_finrank_eq rfl]
    exact Or.inr ⟨((t : ℝ), farArmParameter s1), ⟨t.property, rfl⟩, rfl⟩
  have hRf (t : I01) : c false ((t : ℝ), farArmParameter s0) ∈ frontier M := by
    rw [hM.frontier_eq_of_finrank_eq rfl]
    exact Or.inl (Or.inr ⟨((t : ℝ), farArmParameter s0), ⟨t.property, rfl⟩, rfl⟩)
  have hCf (t : I01) : c true ((t : ℝ), farArmParameter (!s1)) ∈ frontier C := by
    rw [hC.frontier_eq_of_finrank_eq rfl]
    exact Or.inr ⟨((t : ℝ), farArmParameter (!s1)), ⟨t.property, rfl⟩, rfl⟩
  have hselected : ∃ k : NonspanningRetainedPiece,
      D ⊆ interior (chain.retainedSet k) ∧
      ∀ j, j ≠ k → Disjoint (chain.retainedSet j) D := by
    rcases hE with rfl | rfl | rfl
    · refine ⟨.first, hDE, ?_⟩
      intro j hj
      cases j
      · exact (hj rfl).elim
      · exact hAM.symm.mono_right (hDE.trans interior_subset)
      · exact hAC.symm.mono_right (hDE.trans interior_subset)
    · refine ⟨.middle, hDE, ?_⟩
      intro j hj
      cases j
      · exact hAM.mono_right (hDE.trans interior_subset)
      · exact (hj rfl).elim
      · exact hMC.symm.mono_right (hDE.trans interior_subset)
    · refine ⟨.last, hDE, ?_⟩
      intro j hj
      cases j
      · exact hAC.mono_right (hDE.trans interior_subset)
      · exact hMC.mono_right (hDE.trans interior_subset)
      · exact (hj rfl).elim
  obtain ⟨k, hk, hother⟩ := hselected
  obtain ⟨hole⟩ := chain.nonempty_hole hD k hk hother hAf hLf hRf hCf
  exact ⟨⟨A, M, C, s0, s1, hA, hM, hC, hAM, hMC, hAC, hcover,
    h0A, h0M, h1M, h1C, hA1, hC0,
    fun j b ↦ embedded_strip_arm_inter_old_rim (c j) (hcQ j) _ (hfar b), chain, hole⟩⟩

end PoincareConjecture.M76.Dehn
