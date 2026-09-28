import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.StrictContactReduction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.RadialIsotopy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.GenericAxis
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.NoContacts










set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "I" => unitInterval
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem hasJointPLRadialStraightening_of_regular_periodic_axis
    (gamma : C(I, Ann)) (hinj : Function.Injective gamma) (r : ℝ → P2)
    (hr : FinitePiecewiseAffineOn r (Icc 0 1))
    (hr0 : r 0 = (0, -1)) (hr1 : r 1 = (0, 1))
    (hproj : ∀ t : I, annulusMap 8 (by norm_num)
      (((r t).1 : Circle), (r t).2) = gamma t)
    (hheight : ∀ t : I, (r t).2 ∈ Icc (-1 : ℝ) 1)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, (r t).2 ∈ Ioo (-1 : ℝ) 1)
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 32)
    (hfinite : {x ∈ Icc (0 : ℝ) 1 | ∃ k : ℤ, (r x).1 = c + 32 * (k : ℝ)}.Finite)
    (hreg : ∀ (x : ℝ) (k : ℤ), x ∈ Icc (0 : ℝ) 1 → (r x).1 = c + 32 * (k : ℝ) →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, (r y).1 - (c + 32 * (k : ℝ)) = m * (y - x)) :
    HasJointPLRadialStraightening gamma := by
  classical
  generalize hn : {x ∈ Icc (0 : ℝ) 1 | ∃ k : ℤ,
    (r x).1 = c + 32 * (k : ℝ)}.ncard = n
  induction n using Nat.strong_induction_on generalizing gamma r with
  | h n ih =>
    by_cases hcontact : ∃ x ∈ Icc (0 : ℝ) 1, ∃ k : ℤ, (r x).1 = c + 32 * (k : ℝ)
    · obtain ⟨G, r', hG, hr', hi', hr0', hr1', hheight', hproper', hproj',
        htrans', hfinite', hcount, hreg'⟩ :=
        exists_strict_annular_periodic_contact_reduction gamma hinj r hr hr0 hr1
          (fun t ht => hheight ⟨t, ht⟩) hproper hproj hc hfinite hreg hcontact
      have hless : {x ∈ Icc (0 : ℝ) 1 | ∃ k : ℤ,
          (r' x).1 = c + 32 * (k : ℝ)}.ncard < n := by omega
      have hstraight : HasJointPLRadialStraightening
          ⟨fun t => G (gamma t), G.continuous.comp gamma.continuous⟩ :=
        ih _ hless _ (G.injective.comp hinj) r' hr' hr0' hr1' hproj'
          (fun t => hheight' t t.property) hproper' hfinite' hreg' rfl
      exact hstraight.of_isotopy_image gamma G hG
    · exact hasJointPLRadialStraightening_of_no_periodic_contacts gamma hr
        (injOn_annular_lift gamma hinj hproj) hr0 hr1 hproj hheight hproper hc.1 hc.2
        (fun t ht k heq => hcontact ⟨t, ht, k, heq⟩)

theorem hasJointPLRadialStraightening_of_zero_winding_lift
    (gamma : C(I, Ann)) (hinj : Function.Injective gamma) (r : ℝ → P2)
    (hr : FinitePiecewiseAffineOn r (Icc 0 1))
    (hr0 : r 0 = (0, -1)) (hr1 : r 1 = (0, 1))
    (hproj : ∀ t : I, annulusMap 8 (by norm_num)
      (((r t).1 : Circle), (r t).2) = gamma t)
    (hheight : ∀ t : I, (r t).2 ∈ Icc (-1 : ℝ) 1)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, (r t).2 ∈ Ioo (-1 : ℝ) 1) :
    HasJointPLRadialStraightening gamma := by
  obtain ⟨c, hc, hfinite, hreg⟩ := exists_generic_annular_axis
    (hr.postcomp (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap)
  exact hasJointPLRadialStraightening_of_regular_periodic_axis gamma hinj r hr hr0 hr1
    hproj hheight hproper hc hfinite hreg

end PoincareConjecture.M76.Dehn
