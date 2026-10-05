import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.PeriodPositive

/-!
# Actual properness of annular harmonic levels

The classical boundary values exclude both boundary circles from inverse
images of compact subsets of the open potential interval. These inverse
images are therefore closed subsets of the actual compact closed annulus.
Compactness gives quantitative radial separation from both boundaries.
The intermediate value theorem also gives every interior potential value.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareMT.M64Uniformization

open Proofs.M58

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- Inverse images of compact interior potential sets are actual compact subsets of the open
annulus. No boundary regularity beyond continuity is used. Source: Morgan--Tian (2007),
Lemma 19.15, pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-cover-properness.md`. -/
theorem scalarPotential_compact_levels {H : Plane → ℝ} (hHc : Continuous H)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ioo (0 : ℝ) 1) :
    IsCompact (scalarAnnulus ∩ H ⁻¹' K) := by
  have heq : scalarAnnulus ∩ H ⁻¹' K =
      {x : Plane | 0 ≤ scalarAnnulusDefining x} ∩ H ⁻¹' K := by
    ext x
    constructor
    · exact fun hx => ⟨((scalarAnnulusDefining_pos x).mpr hx.1).le, hx.2⟩
    · intro hx
      have hnorm := (scalarAnnulusDefining_nonneg x).mp hx.1
      have hvalue := hKsub hx.2
      refine ⟨⟨lt_of_le_of_ne hnorm.1 ?_, lt_of_le_of_ne hnorm.2 ?_⟩, hx.2⟩
      · intro h
        have hz := hinner x h.symm
        linarith [hvalue.1]
      · intro h
        have ho := houter x h
        linarith [hvalue.2]
  rw [heq]
  exact scalarClosedAnnulus_isCompact.inter_right (hK.isClosed.preimage hHc)

/-- A compact interior range of potential values stays a positive radial distance from each
boundary circle of the actual annulus. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-cover-properness.md`. -/
theorem scalarPotential_levels_radially_separated {H : Plane → ℝ} (hHc : Continuous H)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Ioo (0 : ℝ) 1) :
    ∃ a b : ℝ, 1 < a ∧ a ≤ b ∧ b < 2 ∧
      ∀ x ∈ scalarAnnulus, H x ∈ K → ‖x‖ ∈ Icc a b := by
  let S := scalarAnnulus ∩ H ⁻¹' K
  have hS : IsCompact S := scalarPotential_compact_levels hHc hinner houter hK hKsub
  by_cases hne : S.Nonempty
  · obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn hne continuous_norm.continuousOn
    obtain ⟨q, hq, hmax⟩ := hS.exists_isMaxOn hne continuous_norm.continuousOn
    refine ⟨‖p‖, ‖q‖, hp.1.1, hmin hq, hq.1.2, ?_⟩
    intro x hx hxK
    exact ⟨hmin ⟨hx, hxK⟩, hmax ⟨hx, hxK⟩⟩
  · refine ⟨3 / 2, 3 / 2, by norm_num, le_rfl, by norm_num, ?_⟩
    intro x hx hxK
    exact (hne ⟨x, hx, hxK⟩).elim

/-- Every interior value occurs on an actual radial segment between the two boundary
circles, by the ordinary intermediate value theorem. Source: Morgan--Tian (2007), Lemma
19.15, pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/reports/annular-cover-properness.md`. -/
theorem scalarPotential_surjOn_interval {H : Plane → ℝ} (hHc : Continuous H)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1) :
    SurjOn H scalarAnnulus (Ioo (0 : ℝ) 1) := by
  let f : ℝ → ℝ := fun r => H (r • angularPoint 0)
  have hfc : Continuous f := hHc.comp (continuous_id.smul continuous_const)
  have hf1 : f 1 = 0 := hinner _ (by rw [one_smul, norm_angularPoint])
  have hf2 : f 2 = 1 := houter _ (by
    rw [norm_smul, norm_angularPoint, mul_one]
    norm_num)
  intro u hu
  obtain ⟨r, hr, hru⟩ := intermediate_value_Icc (show (1 : ℝ) ≤ 2 by norm_num)
    hfc.continuousOn (show u ∈ Icc (f 1) (f 2) from by rw [hf1, hf2]; exact ⟨hu.1.le, hu.2.le⟩)
  have hr1 : 1 < r := by
    apply lt_of_le_of_ne hr.1
    intro h
    rw [← h, hf1] at hru
    linarith [hu.1]
  have hr2 : r < 2 := by
    apply lt_of_le_of_ne hr.2
    intro h
    rw [h, hf2] at hru
    linarith [hu.2]
  refine ⟨r • angularPoint 0, ?_, hru⟩
  have hnorm : ‖r • angularPoint 0‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hr1),
      norm_angularPoint, mul_one]
  change 1 < ‖r • angularPoint 0‖ ∧ ‖r • angularPoint 0‖ < 2
  rw [hnorm]
  exact ⟨hr1, hr2⟩

end PoincareMT.M64Uniformization
