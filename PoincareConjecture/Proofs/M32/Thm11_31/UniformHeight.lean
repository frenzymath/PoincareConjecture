import PoincareConjecture.Proofs.M32.Thm11_31.PointwiseHeight
import PoincareConjecture.Proofs.M32.Thm11_31.SelectedLevel
import PoincareConjecture.Proofs.M32.Cor11_36.Selector












set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32




theorem exists_uniform_deepHornHeight
    (P : RepairedHornSelectionPredecessors.{u}) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
        ∀ r₀ C analyticConstant rho delta : ℝ,
          0 < r₀ → 0 < C → 0 < analyticConstant →
          0 < rho → rho < r₀ → 0 < delta →
          ∀ A : RepairedNeckCapTopologyTheory.{u},
            terminalAccuracyFactor * epsilon ≤ A.epsilon₀ →
            ∃ h : ℝ, 0 < h ∧
              UniformDeepHornHeightAtRadius.{u} epsilon C analyticConstant r₀ rho delta h := by
  obtain ⟨epsilonPoint, hPointPos, hPointSmall, hpoint⟩ :=
    exists_uniform_terminalHorn_pointwise_neck_height P
  obtain ⟨tauSelected, hSelectedPos, _hSelectedSmall, hselected⟩ :=
    exists_deepHornConclusion_of_contained_necks.{u}
  let epsilon₀ := min (epsilonPoint / 2) (tauSelected / terminalAccuracyFactor)
  have hPos : 0 < epsilon₀ :=
    lt_min (half_pos hPointPos) (div_pos hSelectedPos terminalAccuracyFactor_pos)
  have hPoint : epsilon₀ ≤ epsilonPoint :=
    (min_le_left _ _).trans (by linarith)
  refine ⟨epsilon₀, hPos, hPoint.trans hPointSmall, ?_⟩
  intro epsilon hepsilon hsmall r₀ C analyticConstant rho delta
    hr₀ hC hAnalytic hrho _hrhor₀ hdelta A hA
  have hpointSmall : epsilon ≤ epsilonPoint := hsmall.trans hPoint
  have hterminal : terminalAccuracyFactor * epsilon ≤ tauSelected :=
    (le_div_iff₀' terminalAccuracyFactor_pos).mp (hsmall.trans (min_le_right _ _))
  let eta := min delta tauSelected
  let b := rho / (2 * C)
  let hUpper := min (rho * eta) (min (rho / 2) (b / 2))
  have heta : 0 < eta := lt_min hdelta hSelectedPos
  have hetadelta : eta ≤ delta := min_le_left _ _
  have hetasmall : eta ≤ tauSelected := min_le_right _ _
  have hb : 0 < b := div_pos hrho (mul_pos (by norm_num) hC)
  have hUpperPos : 0 < hUpper :=
    lt_min (mul_pos hrho heta) (lt_min (half_pos hrho) (half_pos hb))
  obtain ⟨h, hh, hle, hnecks⟩ := hpoint epsilon hepsilon hpointSmall
    r₀ C analyticConstant rho eta hUpper hr₀ hC hAnalytic hrho heta hUpperPos A hA
  have hupper : h ≤ min (rho * delta) (rho / (2 * C)) := by
    apply le_min
    · exact (hle.trans (min_le_left _ _)).trans
        (mul_le_mul_of_nonneg_left hetadelta hrho.le)
    · exact (hle.trans ((min_le_right _ _).trans (min_le_right _ _))).trans
        (by change b / 2 ≤ b; linarith)
  refine ⟨h, hh, hupper, ?_⟩
  intro F T M _ _ _ _ _ _ _ _ H hradius he hconstant hanalytic Q horn hboundary
  have haccuracy : 0 < terminalAccuracyFactor * H.epsilon :=
    mul_pos terminalAccuracyFactor_pos H.epsilon_pos
  have haccuracySmall : terminalAccuracyFactor * H.epsilon ≤ tauSelected := by
    simpa only [he] using hterminal
  have haccuracyA : terminalAccuracyFactor * H.epsilon ≤ A.epsilon₀ := by
    simpa only [he] using hA
  have hheight : h ≤ min (rho * eta)
      (min (rho / 2) ((rho / (2 * H.constant)) / 2)) := by
    simpa only [hconstant] using hle
  obtain ⟨D⟩ := hselected A H Q haccuracy haccuracySmall haccuracyA horn
    H.constant_pos hrho heta hetasmall hh hheight hboundary
    (hnecks H hradius he hconstant hanalytic Q horn hboundary)
  exact ⟨deepHornConclusion_mono D H.constant_pos hrho le_rfl heta hetadelta⟩

end PoincareConjecture.M32
