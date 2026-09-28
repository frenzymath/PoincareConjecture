import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.TerminalStrip
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.WindingCorrection

set_option autoImplicit false
open Set Geometry PLAnnularStrip Topology unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

def HasJointPLRadialStraightening (gamma : C(I, Ann)) : Prop :=
  ∃ (H : I → Ann ≃ₜ Ann) (F Fi : (ℝ × P2) → P2),
    H 0 = Homeomorph.refl Ann ∧
    (∀ t : I, ∀ x : Ann, depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1 → H t x = x) ∧
    Continuous (fun z : I × Ann => H z.1 z.2) ∧
    Continuous (fun z : I × Ann => (H z.1).symm z.2) ∧
    FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
    FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
    (∀ t : I, ∀ x : Ann, F ((t : ℝ), x) = (H t x : P2)) ∧
    (∀ t : I, ∀ x : Ann, Fi ((t : ℝ), x) = ((H t).symm x : P2)) ∧
    ∀ x : Ann, x ∈ range gamma ↔ H 1 x ∈ range (fun t : I => annulusCylinderHomeomorph (t, 0))

theorem hasJointPLRadialStraightening_of_terminal_lift
    (gamma : C(I, Ann)) {r : ℝ → P2}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) (hi : InjOn r (Icc 0 1))
    (hr0 : r 0 = (0, -1)) (hr1 : r 1 = (0, 1))
    (hproj : ∀ t : I, annulusMap 8 (by norm_num) (((r t).1 : Circle), (r t).2) = gamma t)
    (hheight : ∀ t : I, (r t).2 ∈ Icc (-1 : ℝ) 1)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, (r t).2 ∈ Ioo (-1 : ℝ) 1)
    {a b : ℝ} (hwidth : b - a < 32) (hangle : ∀ t : I, (r t).1 ∈ Icc a b) :
    HasJointPLRadialStraightening gamma := by
  let s : ℝ → P2 := Prod.swap ∘ r
  have hs : FinitePiecewiseAffineOn s (Icc 0 1) := hr.postcomp
    (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousAffineEquiv.toContinuousAffineMap
  have hsi : InjOn s (Icc 0 1) := Prod.swap_injective.injOn.comp hi (mapsTo_univ _ _)
  have hs0 : s 0 = ((-1, 0) : P2) := by simp [s, hr0]
  have hs1 : s 1 = ((1, 0) : P2) := by simp [s, hr1]
  let W := s '' Icc (0 : ℝ) 1
  have hW : IsFinitePLBallPair ℝ W {((-1, 0) : P2), (1, 0)} := by
    simpa only [image_pair, hs0, hs1] using
      (isFinitePLBallPair_Icc zero_lt_one).image hs hsi
  have hstrip : W ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc a b := by
    rintro x ⟨t, ht, rfl⟩
    exact ⟨hheight ⟨t, ht⟩, hangle ⟨t, ht⟩⟩
  have hWi : W \ {((-1, 0) : P2), (1, 0)} ⊆ Ioo (-1 : ℝ) 1 ×ˢ univ := by
    rintro x ⟨⟨t, ht, rfl⟩, hn⟩
    have ht0 : t ≠ 0 := by intro h; apply hn; simp [h, hs0]
    have ht1 : t ≠ 1 := by intro h; apply hn; simp [h, hs1]
    exact ⟨hproper t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩, mem_univ _⟩
  obtain ⟨H, F, Fi, hzero, hfixed, hc, hci, hF, hFi, hFv, hFiv, hmem⟩ :=
    exists_joint_PL_annular_terminal_arc_isotopy hW hwidth hstrip hWi
  have himage : annularLiftProjection '' W = range (fun t : I => (gamma t : P2)) := by
    apply Subset.antisymm
    · rintro x ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨⟨t, ht⟩, (hproj ⟨t, ht⟩).symm⟩
    · rintro x ⟨t, rfl⟩
      exact ⟨s t, mem_image_of_mem s t.property, hproj t⟩
  refine ⟨H, F, Fi, hzero, hfixed, hc, hci, hF, hFi, hFv, hFiv, ?_⟩
  intro x
  have h := hmem x
  rw [himage, annularLiftProjection_axis_eq_radial] at h
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨u, hu⟩ := h.mp (mem_range_self t)
    exact ⟨u, Subtype.ext hu⟩
  · rintro ⟨t, ht⟩
    obtain ⟨u, hu⟩ := h.mpr ⟨t, congrArg Subtype.val ht⟩
    exact ⟨u, Subtype.ext hu⟩

theorem exists_zero_winding_lift_with_terminal_straightening
    (gamma : C(I, Ann)) (hinj : Function.Injective gamma)
    (f : ℝ → P2) (hf : FinitePiecewiseAffineOn f (Icc 0 1))
    (hfv : ∀ t : I, f t = (gamma t : P2))
    (hzero : gamma 0 = annulusRimPoint false 0)
    (hone : gamma 1 = annulusRimPoint true 0)
    (hproper : ∀ t : I, (t : ℝ) ∈ Ioo (0 : ℝ) 1 →
      depth 8 (gamma t : P2) ∈ Ioo (-1 : ℝ) 1) :
    ∃ (n : ℤ) (r : ℝ → P2), FinitePiecewiseAffineOn r (Icc 0 1) ∧
      InjOn r (Icc 0 1) ∧ r 0 = (0, -1) ∧ r 1 = (0, 1) ∧
      (∀ t : I, (r t).2 = depth 8 (gamma t : P2)) ∧
      (∀ t : I, annulusMap 8 (by norm_num) (((r t).1 : Circle), (r t).2) =
        (annularIntegerTwist (-n) (gamma t) : P2)) ∧
      (∀ (t s : I) (k : ℤ), r t = r s + (32 * (k : ℝ), 0) → t = s ∧ k = 0) ∧
      ∀ a b : ℝ, b - a < 32 → (∀ t : I, (r t).1 ∈ Icc a b) →
        HasJointPLRadialStraightening
          ((⟨annularIntegerTwist (-n), (annularIntegerTwist (-n)).continuous⟩ : C(Ann, Ann)).comp gamma) := by
  obtain ⟨n, r, hr, hi, hr0, hr1, hdepth, hproj, htranslate⟩ :=
    exists_zero_winding_annular_arc_lift gamma hinj f hf hfv hzero hone
  refine ⟨n, r, hr, hi, hr0, hr1, hdepth, hproj, htranslate, ?_⟩
  intro a b hwidth hangle
  apply hasJointPLRadialStraightening_of_terminal_lift _ hr hi hr0 hr1 hproj
    (fun t => (hdepth t).symm ▸ mem_squareAnnulus_iff_depth.mp (gamma t).property)
    (fun t ht => (hdepth ⟨t, ht.1.le, ht.2.le⟩).symm ▸ hproper ⟨t, ht.1.le, ht.2.le⟩ ht)
    hwidth hangle

end PoincareConjecture.M76.Dehn
