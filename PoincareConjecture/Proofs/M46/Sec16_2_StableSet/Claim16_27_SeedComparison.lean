import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_SquareJoin
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_PrefixAction
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_TailAction
import PoincareConjecture.Proofs.M14.Sec6_3_SquareCornerComparison










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}



theorem admissible_seed_comparison_of_square_tail
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3) (LG : GeneralizedLGeometryConclusion G)
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {B T S tau : ℝ} (hB : 1 ≤ B) {x y : G.Point}
    (path : M14BackwardPath G T 0 S x y) (hmin : M14IsMinimizing path)
    (htau : 0 < tau) (htauS : tau ≤ S)
    (hS : S ≤ surgeryEpochStart (p.i + 1))
    (htotal : tau + seedImageDelay B (p.r (Fin.last p.i)) ≤ surgeryEpochStart (p.i + 1))
    (hscalar : ∀ s ∈ Icc 0 S,
      -6 ≤ horizontalScalarCurvature G.leafwise (path.curve s))
    (hshort : M14BackwardLAction G path ≤ 3 * Real.sqrt S)
    (beta : ℝ → G.Point)
    (hbeta : ContMDiffOn 𝓘(ℝ, ℝ) (spacetimeModel 3) 1 beta
      (Icc (Real.sqrt tau) (Real.sqrt (tau + seedImageDelay B (p.r (Fin.last p.i))))))
    (hbetaClock : ∀ s ∈ Icc (Real.sqrt tau)
      (Real.sqrt (tau + seedImageDelay B (p.r (Fin.last p.i)))),
        G.spacetime.timeFunction (beta s) = T - s ^ 2)
    (hjoin : beta (Real.sqrt tau) = path.curve tau)
    (hbetaDensity : ∀ s ∈ Ioo (Real.sqrt tau)
      (Real.sqrt (tau + seedImageDelay B (p.r (Fin.last p.i)))),
      M14.squareCurveDensity G beta (Icc (Real.sqrt tau)
        (Real.sqrt (tau + seedImageDelay B (p.r (Fin.last p.i))))) s ≤
          2 * s ^ 2 * (4 * (p.r (Fin.last p.i))⁻¹ ^ 2 +
            8 * seedImageRadius B (p.r (Fin.last p.i)) ^ 2 /
              seedImageDelay B (p.r (Fin.last p.i)) ^ 2)) :
    ∃ comparison : M14BackwardPath G T 0
      (tau + seedImageDelay B (p.r (Fin.last p.i))) x
      (beta (Real.sqrt (tau + seedImageDelay B (p.r (Fin.last p.i))))),
      M14BackwardLAction G comparison < actionBudget p / 2 := by
  let d := seedImageDelay B (p.r (Fin.last p.i))
  let rho := seedImageRadius B (p.r (Fin.last p.i))
  let H := surgeryEpochStart (p.i + 1)
  let C := 4 * (p.r (Fin.last p.i))⁻¹ ^ 2 + 8 * rho ^ 2 / d ^ 2
  have hd : 0 < d := seedImageDelay_pos hB (p.r_pos _)
  have htd : 0 < tau + d := add_pos htau hd
  have hH : 0 < H := htd.trans_le htotal
  have hc : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hcb : Real.sqrt tau < Real.sqrt (tau + d) :=
    Real.sqrt_lt_sqrt htau.le (lt_add_of_pos_right _ hd)
  obtain ⟨E0, hE0⟩ := LG.path_calculus.minimizer_euler T 0 S x y path hmin
  obtain ⟨R, _, _⟩ := LG.path_calculus.square_root_regularization T 0 S x y path E0 hE0
  have hsub : Icc 0 (Real.sqrt tau) ⊆ M14SqrtParameterInterval 0 S := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using
      Icc_subset_Icc (le_refl (0 : ℝ)) (Real.sqrt_le_sqrt htauS)
  have hR : ContMDiffOn 𝓘(ℝ, ℝ) (spacetimeModel 3) ∞ R.curve
      (Icc 0 (Real.sqrt tau)) := R.smooth.mono (hsub.trans R.interval_subset)
  have hRc : R.curve (Real.sqrt tau) = path.curve tau := by
    simpa only [Real.sq_sqrt htau.le] using R.agrees _ (hsub ⟨hc.le, le_rfl⟩)
  have hRzero : R.curve 0 = x := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), path.curve_start] using
      R.agrees 0 (hsub ⟨le_rfl, hc.le⟩)
  obtain ⟨gamma, hgamma, hleft, hright, hgammaLeft, hgammaRight⟩ :=
    exists_oneCorner_square_join hc.le hcb.le R.curve beta
      (hR.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)) hbeta (hRc.trans hjoin.symm)
  have hclock : ∀ s ∈ Icc 0 (Real.sqrt (tau + d)),
      G.spacetime.timeFunction (gamma s) = T - s ^ 2 := by
    intro s hs
    by_cases hsc : s ≤ Real.sqrt tau
    · rw [hleft ⟨hs.1, hsc⟩]
      exact R.curve_time s (hsub ⟨hs.1, hsc⟩)
    · rw [hright ⟨(lt_of_not_ge hsc).le, hs.2⟩]
      exact hbetaClock s ⟨(lt_of_not_ge hsc).le, hs.2⟩
  obtain ⟨partition, hvelocity⟩ := oneCorner_gauge_primitive_partition
    (Real.sqrt_pos.mpr htd) hc.le hcb.le gamma hgamma hgammaLeft hgammaRight
  obtain ⟨hint, haction⟩ := oneCorner_gauge_action_eq hM12 gamma hgamma
    hgammaLeft hgammaRight partition hvelocity
  let D := M14.squareCurveDensity G gamma (Icc 0 (Real.sqrt (tau + d)))
  have hIntLeft : IntervalIntegrable D volume 0 (Real.sqrt tau) := hint.mono_set (by
    rw [uIcc_of_le hc.le, uIcc_of_le (Real.sqrt_nonneg _)]
    exact Icc_subset_Icc_right hcb.le)
  have hIntRight : IntervalIntegrable D volume (Real.sqrt tau) (Real.sqrt (tau + d)) :=
    hint.mono_set (by
      rw [uIcc_of_le hcb.le, uIcc_of_le (Real.sqrt_nonneg _)]
      exact Icc_subset_Icc_left hc.le)
  have hprefixEq : (∫ s in 0..Real.sqrt tau, D s) =
      M14BackwardLAction G (M14.prefixPath path tau htau htauS) := by
    have heq : (∫ s in 0..Real.sqrt tau, D s) = ∫ s in 0..Real.sqrt tau,
        M14.squareCurveDensity G R.curve (Icc 0 (Real.sqrt tau)) s := by
      apply intervalIntegral.integral_congr_Ioo_of_le hc.le
      intro s hs
      apply squareCurveDensity_germ_eq
        (Icc_mem_nhds hs.1 (hs.2.trans_le hcb.le)) (Icc_mem_nhds hs.1 hs.2)
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with z hz
      exact hleft hz
    rw [heq]
    have h := M14.integral_squareCurveDensity_eq_action_of_curve hM12
      (M14.prefixPath path tau htau htauS) R.curve
      (by simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using hR)
      (fun s hs => R.curve_time s (hsub (by
        simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using hs)))
      (fun t ht => by
        have hs : Real.sqrt t ∈ Icc 0 (Real.sqrt tau) :=
          ⟨Real.sqrt_nonneg t, Real.sqrt_le_sqrt ht.2⟩
        change R.curve (Real.sqrt t) = path.curve t
        simpa only [Real.sq_sqrt ht.1] using R.agrees _ (hsub hs))
    simpa only [Real.sqrt_zero, M14SqrtParameterInterval] using h
  have htailBound : (∫ s in Real.sqrt tau..Real.sqrt (tau + d), D s) ≤
      Real.sqrt H * d * C := by
    apply seed_square_tail_action_le htau.le hd.le htotal (by dsimp [C]; positivity) hIntRight
    intro s hs
    have hsame : D s = M14.squareCurveDensity G beta
        (Icc (Real.sqrt tau) (Real.sqrt (tau + d))) s := by
      apply squareCurveDensity_germ_eq (Icc_mem_nhds (hc.trans hs.1) hs.2)
        (Icc_mem_nhds hs.1 hs.2)
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with z hz
      exact hright hz
    rw [hsame]
    exact hbetaDensity s hs
  have hprefixBound := prefix_action_budget_margin p path htau htauS hS hscalar hshort
  have hcoefficient : d * C ≤ 129 / 512 := seed_tail_coefficient_bound hB (p.r_pos _)
  have htailShort := mul_le_mul_of_nonneg_left hcoefficient (Real.sqrt_nonneg H)
  have htotalAction : partition.action ≤
      actionBudget p / 2 - Real.sqrt H + Real.sqrt H * (129 / 512) := by
    rw [haction, ← intervalIntegral.integral_add_adjacent_intervals hIntLeft hIntRight,
      hprefixEq]
    nlinarith
  obtain ⟨q, hq⟩ := gauge_primitive_recovery_sequence hM12 htd gamma hgamma hclock partition
  have hmargin : partition.action < actionBudget p / 2 := by
    have hroot := Real.sqrt_pos.mpr hH
    linarith
  obtain ⟨k, hk⟩ := (hq.eventually_lt_const hmargin).exists
  have hstart : gamma 0 = x := (hleft ⟨le_rfl, hc.le⟩).trans hRzero
  have hend : gamma (Real.sqrt (tau + d)) = beta (Real.sqrt (tau + d)) :=
    hright ⟨hcb.le, le_rfl⟩
  have hresult : ∃ comparison : M14BackwardPath G T 0 (tau + d)
      (gamma 0) (gamma (Real.sqrt (tau + d))),
      M14BackwardLAction G comparison < actionBudget p / 2 := ⟨q k, hk⟩
  rw [hstart, hend] at hresult
  exact hresult

end PoincareConjecture.Proofs.M46
