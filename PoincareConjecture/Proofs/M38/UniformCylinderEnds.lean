import PoincareConjecture.Proofs.M38.CylinderEndReparametrization









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology Filter
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

variable (A : UnitTwoSphere → ℝ) (hA : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ A)

include hA


theorem exists_cylinderEndScale (hpos : ∀ z : UnitTwoSphere, 0 < A z) :
    ∃ k : ℝ, 0 < k ∧ k ≤ 1 / 2 ∧ ∀ z : UnitTwoSphere, k < A z := by
  obtain ⟨m, hm, hmin⟩ := isCompact_univ.exists_forall_le'
    hA.continuous.continuousOn (fun z (_ : z ∈ Set.univ) => hpos z)
  let k : ℝ := min (1 / 4) (m / 2)
  have hk : 0 < k := lt_min (by norm_num) (by positivity)
  refine ⟨k, hk, (min_le_left _ _).trans (by norm_num), ?_⟩
  intro z
  have hkm : k ≤ m / 2 := min_le_right _ _
  have hmz : m ≤ A z := hmin z (Set.mem_univ _)
  linarith

variable (k : ℝ) (hk : 0 < k) (hk2 : k ≤ 1 / 2)
  (hAk : ∀ z : UnitTwoSphere, k < A z)

include hk hk2 hAk



theorem exists_uniformCylinderEndRange :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 8 ∧
      ∀ z : UnitTwoSphere, ∀ s : ℝ, 0 < s → s < η →
        A z * punctureRadialOrderIso (1 + s) ≤ 5 / 32 ∧
        k * punctureRadialOrderIso (1 + s) ≤ 1 / 8 := by
  obtain ⟨M, hM, hbound⟩ := (isCompact_range hA.continuous).isBounded.exists_pos_norm_le
  have hAM (z : UnitTwoSphere) : A z ≤ M :=
    (le_abs_self (A z)).trans (by
      simpa only [Real.norm_eq_abs] using hbound (A z) ⟨z, rfl⟩)
  let ε : ℝ := min (5 / (32 * M)) (1 / (8 * k))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hP : Continuous (fun s : ℝ => punctureRadialOrderIso (1 + s)) :=
    punctureRadialOrderIso_smooth.continuous.comp (continuous_const.add continuous_id)
  have hn : {s : ℝ | punctureRadialOrderIso (1 + s) < ε} ∈ 𝓝 (0 : ℝ) :=
    (isOpen_lt hP continuous_const).mem_nhds (by
      simpa only [Set.mem_setOf_eq, add_zero, punctureRadialOrderIso_one] using hε)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hn
  let η : ℝ := min δ (1 / 8)
  refine ⟨η, lt_min hδ (by norm_num), min_le_right _ _, ?_⟩
  intro z s hs hsη
  have hsδ : s < δ := hsη.trans_le (min_le_left _ _)
  have hPs : punctureRadialOrderIso (1 + s) < ε := hδsub (by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hs] using hsδ)
  have hP0 : 0 < punctureRadialOrderIso (1 + s) :=
    (punctureRadialOrderIso_pos_iff _).mpr (by linarith)
  have hPM := (lt_div_iff₀ (by positivity : 0 < 32 * M)).mp
    (hPs.trans_le (min_le_left _ _))
  have hPk := (lt_div_iff₀ (by positivity : 0 < 8 * k)).mp
    (hPs.trans_le (min_le_right _ _))
  refine ⟨?_, ?_⟩
  · have hmul := mul_le_mul_of_nonneg_right (hAM z) hP0.le
    nlinarith
  · nlinarith


theorem cylinderEndDiffeomorph_uniform_formulas :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 8 ∧
      (∀ z : UnitTwoSphere, ∀ s : ℝ, 0 < s → s < η →
        cylinderEndDiffeomorph A k hA hk hk2 hAk (z, s / (1 + s)) = (z, k * s)) ∧
      (∀ z : UnitTwoSphere, ∀ s : ℝ, 0 < s → s < η →
        cylinderEndDiffeomorph A k hA hk hk2 hAk
          (z, 1 - A z * punctureRadialOrderIso (1 + s)) = (z, 1 - k * s)) := by
  obtain ⟨η, hη, hη8, hsmall⟩ := exists_uniformCylinderEndRange A hA k hk hk2 hAk
  refine ⟨η, hη, hη8, ?_, ?_⟩
  · intro z s hs hsη
    exact cylinderEndDiffeomorph_lower A k hA hk hk2 hAk z hs (hsη.le.trans hη8)
  · intro z s hs hsη
    exact cylinderEndDiffeomorph_upper A k hA hk hk2 hAk z
      (hsmall z s hs hsη).1 (hsmall z s hs hsη).2

omit k hk hk2 hAk in


theorem exists_cylinderEndReparametrization (hpos : ∀ z : UnitTwoSphere, 0 < A z) :
    ∃ G : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      RoundCylinderSpace RoundCylinderSpace ∞,
    ∃ k η : ℝ, 0 < k ∧ k ≤ 1 / 2 ∧ 0 < η ∧ η ≤ 1 / 8 ∧
      G '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) = Set.univ ×ˢ Set.Ioo (0 : ℝ) 1 ∧
      (∀ p : RoundCylinderSpace, (G p).1 = p.1) ∧
      (∀ z : UnitTwoSphere, ∀ s : ℝ, 0 < s → s < η →
        G (z, s / (1 + s)) = (z, k * s)) ∧
      (∀ z : UnitTwoSphere, ∀ s : ℝ, 0 < s → s < η →
        G (z, 1 - A z * punctureRadialOrderIso (1 + s)) = (z, 1 - k * s)) := by
  obtain ⟨k, hk, hk2, hAk⟩ := exists_cylinderEndScale A hA hpos
  obtain ⟨η, hη, hη8, hlower, hupper⟩ :=
    cylinderEndDiffeomorph_uniform_formulas A hA k hk hk2 hAk
  refine ⟨cylinderEndDiffeomorph A k hA hk hk2 hAk, k, η, hk, hk2, hη, hη8,
    cylinderEndDiffeomorph_image_strip A k hA hk hk2 hAk, ?_, hlower, hupper⟩
  intro p
  rfl

end PoincareConjecture.M38
