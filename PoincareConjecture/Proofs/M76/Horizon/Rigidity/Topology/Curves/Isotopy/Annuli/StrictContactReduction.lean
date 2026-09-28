import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.ProjectedTwoMoves
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.LiftGermTransfer
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.SignedReduction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.MovedGeometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.LiftGeometry



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "I" => unitInterval
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem annular_lift_mem_radial_iff (x : Ann) (r : P2) (c : ℝ)
    (hr : r.2 ∈ Icc (-1 : ℝ) 1)
    (hproj : annulusMap 8 (by norm_num) ((r.1 : Circle), r.2) = x) :
    x ∈ range (fun t : I => annulusCylinderHomeomorph (t, (c : Circle))) ↔
      ∃ k : ℤ, r.1 = c + 32 * (k : ℝ) := by
  constructor
  · rintro ⟨t, ht⟩
    have heq := hproj.trans (congrArg Subtype.val ht).symm
    dsimp only at heq
    rw [annulusCylinderHomeomorph_apply] at heq
    have hp := congrArg Prod.fst (injective_annulusMap (L := 8) (d := 1)
      (by norm_num) (by norm_num)
      (a₁ := ((r.1 : Circle), ⟨r.2, hr⟩))
      (a₂ := ((c : Circle), ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.property.1, t.property.2]⟩)) heq)
    change (r.1 : Circle) = (c : Circle) at hp
    have hz : ((r.1 - c : ℝ) : Circle) = 0 := by rw [AddCircle.coe_sub, hp, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (4 * (8 : ℝ))).mp hz
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul] at hk
    linarith
  · rintro ⟨k, hk⟩
    let t : I := ⟨(r.2 + 1) / 2, by constructor <;> linarith [hr.1, hr.2]⟩
    refine ⟨t, Subtype.ext ?_⟩
    dsimp only
    rw [annulusCylinderHomeomorph_apply, ← hproj]
    have hp : ((32 * (k : ℝ) : ℝ) : Circle) = 0 :=
      (AddCircle.coe_eq_zero_iff (4 * (8 : ℝ))).mpr ⟨k, by simp [zsmul_eq_mul]; ring⟩
    rw [hk, AddCircle.coe_add, hp, add_zero]
    change annulusMap 8 (by norm_num) ((c : Circle), 2 * (t : ℝ) - 1) =
      annulusMap 8 (by norm_num) ((c : Circle), r.2)
    congr 2
    change 2 * ((r.2 + 1) / 2) - 1 = r.2
    ring

theorem exists_strict_annular_periodic_contact_reduction
    (gamma : C(I, Ann)) (hinj : Function.Injective gamma)
    (r : ℝ → P2) (hr : FinitePiecewiseAffineOn r (Icc 0 1))
    (hr0 : r 0 = (0, -1)) (hr1 : r 1 = (0, 1))
    (hheight : ∀ t ∈ Icc (0 : ℝ) 1, (r t).2 ∈ Icc (-1 : ℝ) 1)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, (r t).2 ∈ Ioo (-1 : ℝ) 1)
    (hproj : ∀ t : I, annulusMap 8 (by norm_num) (((r t).1 : Circle), (r t).2) = gamma t)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 32)
    (hfinite : {x ∈ Icc (0 : ℝ) 1 | ∃ k : ℤ, (r x).1 = c + 32 * (k : ℝ)}.Finite)
    (hreg : ∀ (x : ℝ) (k : ℤ), x ∈ Icc (0 : ℝ) 1 → (r x).1 = c + 32 * (k : ℝ) →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, (r y).1 - (c + 32 * (k : ℝ)) = m * (y - x))
    (hcontact : ∃ x ∈ Icc (0 : ℝ) 1, ∃ k : ℤ, (r x).1 = c + 32 * (k : ℝ)) :
    ∃ (G : Ann ≃ₜ Ann) (r' : ℝ → P2), HasJointPLAnnularIsotopy G ∧
      FinitePiecewiseAffineOn r' (Icc 0 1) ∧ InjOn r' (Icc 0 1) ∧
      r' 0 = (0, -1) ∧ r' 1 = (0, 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, (r' t).2 ∈ Icc (-1 : ℝ) 1) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, (r' t).2 ∈ Ioo (-1 : ℝ) 1) ∧
      (∀ t : I, annulusMap 8 (by norm_num) (((r' t).1 : Circle), (r' t).2) = G (gamma t)) ∧
      (∀ (s t : ℝ), s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
        ∀ k : ℤ, r' s = r' t + (32 * (k : ℝ), 0) → s = t ∧ k = 0) ∧
      {x ∈ Icc (0 : ℝ) 1 | ∃ k : ℤ, (r' x).1 = c + 32 * (k : ℝ)}.Finite ∧
      {x ∈ Icc (0 : ℝ) 1 | ∃ k : ℤ, (r' x).1 = c + 32 * (k : ℝ)}.ncard + 2 =
        {x ∈ Icc (0 : ℝ) 1 | ∃ k : ℤ, (r x).1 = c + 32 * (k : ℝ)}.ncard ∧
      ∀ (x : ℝ) (k : ℤ), x ∈ Icc (0 : ℝ) 1 → (r' x).1 = c + 32 * (k : ℝ) →
        ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
          ∀ y ∈ Icc a b, (r' y).1 - (c + 32 * (k : ℝ)) = m * (y - x) := by
  obtain ⟨n, lo, hi, D, E, H, J, F, Fi, Q, Qi, _, hlo, hhi, _, hwidth,
    hD, hE, hstrip, hH0, hJ0, hHc, hHci, hJc, hJci, hHfix, hJfix,
    hFv, hFiv, hQv, hQiv, hPL, hfin, hcount, hregular⟩ :=
    exists_strict_plane_periodic_contact_reduction_of_nonempty hr
      (injOn_annular_lift gamma hinj hproj) hheight hproper
      (congrArg Prod.snd hr0) (congrArg Prod.snd hr1)
      (congrArg Prod.fst hr0) (congrArg Prod.fst hr1)
      (annular_lift_translate_separation gamma hinj hproj) hc hfinite hreg hcontact
  have hfinite_tracks {S : Set P2} (hS : IsFinitePLBallPair P2 S (frontier S)) :
      FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ S) ∧
      FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ S) ∧
      FinitePiecewiseAffineOn Q (Icc (0 : ℝ) 1 ×ˢ S) ∧
      FinitePiecewiseAffineOn Qi (Icc (0 : ℝ) 1 ×ˢ S) := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hS
    rw [← hKs]
    exact hPL K hK
  obtain ⟨G, hG, hwindow, hcontacts⟩ := exists_projected_two_moves (c + 32 * (n : ℝ))
    hD hE hwidth hlo.le hhi.le hstrip H J hH0 hJ0 hHfix hJfix hHc hHci hJc hJci
    F Fi Q Qi (hfinite_tracks hD).1 (hfinite_tracks hD).2.1
    (hfinite_tracks hE).2.2.1 (hfinite_tracks hE).2.2.2
    (fun t z => hFv t z) (fun t z => hFiv t z)
    (fun t z => hQv t z) (fun t z => hQiv t z)
  obtain ⟨hg0, hg1⟩ := annular_lift_zero_winding_endpoints gamma hproj hr0 hr1
  have hproperGamma (t : I) (ht : (t : ℝ) ∈ Ioo (0 : ℝ) 1) :
      depth 8 (gamma t : P2) ∈ Ioo (-1 : ℝ) 1 := by
    rw [← hproj, depth_annulusMap (by norm_num)
      (by have hh := abs_le.mpr (hheight t t.property); linarith)]
    exact hproper t ht
  obtain ⟨r', hr', hi', hr'0, hr'1, _, hheight', hproper', hproj', htranslate'⟩ :=
    exists_proper_zero_winding_lift_after_joint_PL_isotopy gamma hinj
      (fun t => annulusMap 8 (by norm_num) (((r t).1 : Circle), (r t).2))
      (finitePL_projected_annular_lift hr (fun t => hheight t t.property)) hproj
      hg0 hg1 hproperGamma r hr hr0 hr1 (fun t => hheight t t.property) hproj G hG
  have hphase : ((c + 32 * (n : ℝ) : ℝ) : Circle) = (c : Circle) := by
    have hp : ((32 * (n : ℝ) : ℝ) : Circle) = 0 :=
      (AddCircle.coe_eq_zero_iff (4 * (8 : ℝ))).mpr ⟨n, by simp [zsmul_eq_mul]; ring⟩
    rw [AddCircle.coe_add, hp, add_zero]
  have hequiv (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      (∃ k : ℤ, (r' x).1 = c + 32 * (k : ℝ)) ↔
      ∃ j : ℤ, (J 1 (H 1 (annularLiftAboveAxis r (c + 32 * (n : ℝ) + 32 * (j : ℝ)) x))).2 = 0 := by
    rw [← annular_lift_mem_radial_iff (G (gamma ⟨x, hx⟩)) (r' x) c (hheight' x hx)
      (hproj' ⟨x, hx⟩)]
    have hh := hcontacts (gamma ⟨x, hx⟩) (r x) (hheight x hx) (hproj ⟨x, hx⟩).symm
    rw [hphase] at hh
    exact hh
  have hsets : {x ∈ Icc (0 : ℝ) 1 | ∃ k : ℤ, (r' x).1 = c + 32 * (k : ℝ)} =
      {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ,
        (J 1 (H 1 (annularLiftAboveAxis r (c + 32 * (n : ℝ) + 32 * (j : ℝ)) x))).2 = 0} := by
    ext x
    exact and_congr_right (hequiv x)
  refine ⟨G, r', hG, hr', hi', hr'0, hr'1, hheight', hproper', hproj', htranslate',
    hsets.symm ▸ hfin, ?_, ?_⟩
  · rw [hsets]
    exact hcount
  · intro x k hx hk
    obtain ⟨j, hj⟩ := (hequiv x hx).mp ⟨k, hk⟩
    obtain ⟨u, v, m, hu, hux, hxv, hv, hm, hgerm⟩ := hregular j x hx hj
    exact exists_affine_lift_germ_of_common_window hlo hhi
      (fun z hz => ⟨Ioo_subset_Icc_self (hstrip (Or.inl hz)).1, (hstrip (Or.inl hz)).2⟩)
      (fun z hz => ⟨Ioo_subset_Icc_self (hstrip (Or.inr hz)).1, (hstrip (Or.inr hz)).2⟩)
      (H 1) (J 1) (hHfix 1) (hJfix 1) G hwindow gamma r r' hr.continuousOn hr'.continuousOn
      (fun t => hheight t t.property) (fun t => hheight' t t.property) hproj hproj'
      j hu hux hxv hv hm hj hgerm hk

end PoincareConjecture.M76.Dehn
