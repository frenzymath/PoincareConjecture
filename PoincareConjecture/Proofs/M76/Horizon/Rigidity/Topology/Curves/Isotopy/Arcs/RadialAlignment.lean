import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.TerminalStrip
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.SupportedAnnularDisk









set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Geometry PLAnnularStrip Topology unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "p₀" => ((-1, 0) : P2)
local notation "p₁" => ((1, 0) : P2)

private theorem radial_segment_isFinitePLBallPair :
    IsFinitePLBallPair ℝ (segment ℝ p₀ p₁) {p₀, p₁} := by
  have h := isFinitePLBallPair_affine_interval zero_lt_one
    (ContinuousAffineMap.lineMap p₀ p₁)
    (AffineMap.lineMap_injective ℝ (show p₀ ≠ p₁ by
      intro h
      have := congrArg Prod.fst h
      norm_num at this)).injOn
  simpa only [ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one, ← segment_eq_image_lineMap] using h

theorem exists_joint_PL_annular_radial_parameter_alignment
    (G : Ann ≃ₜ Ann) (hG : G.IsFinitePL)
    (hfix : ∀ x : Ann, depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1 → G x = x)
    (hmem : ∀ x : Ann, x ∈ range (fun t : I => annulusCylinderHomeomorph (t, 0)) ↔
      G x ∈ range (fun t : I => annulusCylinderHomeomorph (t, 0))) :
    ∃ (H : I → Ann ≃ₜ Ann) (F Fi : (ℝ × P2) → P2),
      H 0 = Homeomorph.refl Ann ∧
      (∀ t : I, ∀ x : Ann, depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1 → H t x = x) ∧
      Continuous (fun z : I × Ann => H z.1 z.2) ∧
      Continuous (fun z : I × Ann => (H z.1).symm z.2) ∧
      FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
      FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
      (∀ t : I, ∀ x : Ann, F ((t : ℝ), x) = (H t x : P2)) ∧
      (∀ t : I, ∀ x : Ann, Fi ((t : ℝ), x) = ((H t).symm x : P2)) ∧
      ∀ t : I, H 1 (G (annulusCylinderHomeomorph (t, 0))) = annulusCylinderHomeomorph (t, 0) := by
  have hstrip : segment ℝ p₀ p₁ ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
    ((convex_Icc _ _).prod (convex_Icc _ _)).segment_subset (by norm_num) (by norm_num)
  have haxis : ∀ x ∈ segment ℝ p₀ p₁, x.2 = 0 := by
    intro x hx
    exact (((convex_univ : Convex ℝ (univ : Set ℝ)).prod (convex_singleton (0 : ℝ))).segment_subset
      (show p₀ ∈ (univ ×ˢ ({0} : Set ℝ)) by simp)
      (show p₁ ∈ (univ ×ˢ ({0} : Set ℝ)) by simp) hx).2
  have hproper : segment ℝ p₀ p₁ \ {p₀, p₁} ⊆ Ioo (-1 : ℝ) 1 ×ˢ univ := by
    intro x hx
    refine ⟨⟨lt_of_le_of_ne (hstrip hx.1).1.1 ?_,
      lt_of_le_of_ne (hstrip hx.1).1.2 ?_⟩, mem_univ _⟩
    · intro h
      exact hx.2 (Or.inl (Prod.ext h.symm (haxis x hx.1)))
    · intro h
      exact hx.2 (Or.inr (Prod.ext h (haxis x hx.1)))
  obtain ⟨S, hS, hSAnn, hp₀, hp₁, hpne, hR, _, hproperR, _, hrimS⟩ :=
    exists_annular_terminal_strip_support radial_segment_isFinitePLBallPair
      (by norm_num : (1 : ℝ) - -1 < 32) hstrip hproper
  let R := annularLiftProjection '' segment ℝ p₀ p₁
  have hRS : R ⊆ S := by
    intro x hx
    by_cases he : x ∈ ({annularLiftProjection p₀, annularLiftProjection p₁} : Set P2)
    · rcases he with rfl | rfl
      · exact hS.1 hp₀
      · exact hS.1 hp₁
    · exact (hproperR ⟨hx, he⟩).1
  have hRAnn : R ⊆ Ann := hRS.trans hSAnn
  have hrange (x : Ann) : (x : P2) ∈ R ↔
      x ∈ range (fun t : I => annulusCylinderHomeomorph (t, 0)) := by
    rw [show R = range (fun t : I => (annulusCylinderHomeomorph (t, 0) : P2)) from
      annularLiftProjection_axis_eq_radial]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, Subtype.ext ht⟩
    · rintro ⟨t, rfl⟩
      exact mem_range_self t
  have hmemInv (x : Ann) : (x : P2) ∈ R ↔ (G.symm x : P2) ∈ R := by
    rw [hrange, hrange]
    have h := hmem (G.symm x)
    rw [G.apply_symm_apply] at h
    exact h.symm
  let q : R ≃ₜ R := G.symm.restrictSubsets hRAnn hRAnn hmemInv
  have hRcopy := hR
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hRcopy
  have hq : q.IsFinitePL := hG.symm.restrictSubsets hRAnn hRAnn hmemInv K hK hKs
  have hqval (x : R) : (q x : P2) = (G.symm ⟨x, hRAnn x.property⟩ : P2) := rfl
  have hqends (x : R)
      (hx : (x : P2) ∈ ({annularLiftProjection p₀, annularLiftProjection p₁} : Set P2)) :
      (q x : P2) = x := by
    have hd : depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1 := by
      rcases hx with hx | hx
      · rw [hx]
        left
        exact depth_annulusMap (by norm_num) (by norm_num) _
      · rw [hx]
        right
        exact depth_annulusMap (by norm_num) (by norm_num) _
    have hg : G.symm ⟨x, hRAnn x.property⟩ = ⟨x, hRAnn x.property⟩ := by
      apply G.injective
      rw [G.apply_symm_apply, hfix _ hd]
    exact (hqval x).trans (congrArg Subtype.val hg)
  obtain ⟨e, he, _, hefix, hkeep, _⟩ :=
    exists_finitePL_proper_arc_replacement_fix_rim hS hR hR hp₀ hp₁ hpne
      hproperR hproperR q hq hqends
  obtain ⟨H, F, Fi, hzero, hfixed, _, hc, hci, hF, hFi, hFv, hFiv, hHe⟩ :=
    exists_joint_PL_supported_annular_disk_isotopy hS hSAnn hrimS e he hefix
  refine ⟨H, F, Fi, hzero, hfixed, hc, hci, hF, hFi, hFv, hFiv, ?_⟩
  intro t
  let x := G (annulusCylinderHomeomorph (t, 0))
  have hxR : (x : P2) ∈ R := (hrange x).mpr ((hmem _).mp (mem_range_self t))
  apply Subtype.ext
  exact (congrArg (fun y : Ann => (y : P2)) (hHe ⟨x, hRS hxR⟩)).trans
    ((hkeep ⟨x, hxR⟩ (hRS hxR)).trans
      ((hqval ⟨x, hxR⟩).trans (congrArg Subtype.val (G.symm_apply_apply _))))

end PoincareConjecture.M76.Dehn
