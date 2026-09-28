import PoincareConjecture.Proofs.M32.Cor11_36.Restriction
import PoincareConjecture.Proofs.M32.Mathlib.MonotoneSelection

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

theorem hornBoundaryBelow_of_le
    {F : GeneralizedRicciFlowData.{u}} {T epsilon rho sigma : ℝ}
    {E : GeneralizedFlowExtension F T} {horn : StrongHorn E epsilon}
    (hr : 0 < rho) (hrs : rho ≤ sigma) (hb : HornBoundaryBelow horn sigma) :
    HornBoundaryBelow horn rho := by
  intro x hx
  exact (hb x hx).trans (pow_le_pow_left₀ (inv_nonneg.mpr (hr.trans_le hrs).le)
    ((inv_le_inv₀ (hr.trans_le hrs) hr).2 hrs) 2)

def UniformDeepHornHeight (epsilon C analyticConstant rho delta a : ℝ) : Prop :=
  a ≤ min (rho * delta) (rho / (2 * C)) ∧
    ∀ {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
      {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M],
      ∀ H : SingularTimeAssumptions F T M,
        rho < H.r₀ → H.epsilon = epsilon → H.constant = C →
        H.analytic_constant = analyticConstant →
        ∀ Q : SingularLimitConclusion H,
          ∀ horn : StrongHorn Q.extension (terminalAccuracyFactor * H.epsilon),
            HornBoundaryBelow horn (rho / (2 * H.constant)) →
              Nonempty (DeepHornNeckConclusion Q.extension
                (terminalAccuracyFactor * H.epsilon) H.constant rho delta horn a)

def UniformDeepHornHeightAtRadius
    (epsilon C analyticConstant r₀ rho delta a : ℝ) : Prop :=
  a ≤ min (rho * delta) (rho / (2 * C)) ∧
    ∀ {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
      {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] [SecondCountableTopology M],
      ∀ H : SingularTimeAssumptions F T M,
        H.r₀ = r₀ → H.epsilon = epsilon → H.constant = C →
        H.analytic_constant = analyticConstant →
        ∀ Q : SingularLimitConclusion H,
          ∀ horn : StrongHorn Q.extension (terminalAccuracyFactor * H.epsilon),
            HornBoundaryBelow horn (rho / (2 * H.constant)) →
              Nonempty (DeepHornNeckConclusion Q.extension
                (terminalAccuracyFactor * H.epsilon) H.constant rho delta horn a)

theorem uniformDeepHornHeight_mono
    {epsilon C analyticConstant rho sigma delta eta a : ℝ}
    (hC : 0 < C) (hr : 0 < rho) (hd : 0 < delta)
    (hrs : rho ≤ sigma) (hde : delta ≤ eta)
    (G : UniformDeepHornHeight.{u} epsilon C analyticConstant rho delta a) :
    UniformDeepHornHeight.{u} epsilon C analyticConstant sigma eta a := by
  refine ⟨G.1.trans (min_le_min
    (mul_le_mul hrs hde hd.le (hr.trans_le hrs).le)
    (div_le_div_of_nonneg_right hrs (by positivity))), ?_⟩
  intro F T M _ _ _ _ _ _ _ _ H hs he hconstant hanalytic Q horn hb
  have hden : 0 < 2 * H.constant := mul_pos (by norm_num) H.constant_pos
  have hcut : rho / (2 * H.constant) ≤ sigma / (2 * H.constant) :=
    div_le_div_of_nonneg_right hrs hden.le
  obtain ⟨D⟩ := G.2 H (hrs.trans_lt hs) he hconstant hanalytic Q horn
    (hornBoundaryBelow_of_le (div_pos hr hden) hcut hb)
  exact ⟨deepHornConclusion_mono D H.constant_pos hr hrs hd hde⟩

theorem exists_deepHornScaleSelection_of_uniformHeight
    {epsilon C analyticConstant : ℝ} (hC : 0 < C)
    (hlocal : ∀ rho delta : ℝ, 0 < rho → 0 < delta →
      ∃ b : ℝ, 0 < b ∧ ∀ a : ℝ, 0 < a → a ≤ b →
        UniformDeepHornHeight.{u} epsilon C analyticConstant rho delta a) :
    Nonempty (M32DeepHornScaleSelection.{u} epsilon C analyticConstant) := by
  obtain ⟨h, hpos, hmonoR, hmonoD, hgood⟩ := exists_monotone_height_selection
    (UniformDeepHornHeight.{u} epsilon C analyticConstant)
    (fun hr hd hrs hde G => uniformDeepHornHeight_mono hC hr hd hrs hde G) hlocal
  refine ⟨{
    h := h
    h_pos := hpos
    h_le := ?_
    h_mono_rho := fun delta _ => (hmonoR delta).monotoneOn _
    h_mono_delta := fun rho _ => (hmonoD rho).monotoneOn _
    h_upper := ?_
    deep_horn := fun rho delta a hr hd ha hab => (hgood rho delta a hr hd ha hab).2 }⟩
  · intro rho delta hr hd
    exact (hgood rho delta (h rho delta) hr hd (hpos rho delta hr hd) le_rfl).1.trans
      (min_le_left _ _)
  · intro rho delta hr hd
    exact (hgood rho delta (h rho delta) hr hd (hpos rho delta hr hd) le_rfl).1.trans
      (min_le_right _ _)

theorem uniformHeight_of_restrictRadius
    {epsilon C analyticConstant : ℝ} (hC : 0 < C)
    (hlocal : ∀ r₀ rho delta : ℝ, 0 < r₀ → 0 < rho → rho < r₀ → 0 < delta →
      ∃ b : ℝ, 0 < b ∧ ∀ a : ℝ, 0 < a → a ≤ b →
        UniformDeepHornHeightAtRadius.{u} epsilon C analyticConstant r₀ rho delta a) :
    ∀ rho delta : ℝ, 0 < rho → 0 < delta →
      ∃ b : ℝ, 0 < b ∧ ∀ a : ℝ, 0 < a → a ≤ b →
        UniformDeepHornHeight.{u} epsilon C analyticConstant rho delta a := by
  intro rho delta hr hd
  have hhalf : 0 < rho / 2 := half_pos hr
  have hhalf_lt : rho / 2 < rho := half_lt_self hr
  obtain ⟨b, hb, hg⟩ := hlocal rho (rho / 2) delta hr hhalf hhalf_lt hd
  refine ⟨b, hb, ?_⟩
  intro a ha hab
  obtain ⟨hbound, hgeom⟩ := hg a ha hab
  refine ⟨hbound.trans (min_le_min
    (mul_le_mul_of_nonneg_right hhalf_lt.le hd.le)
    (div_le_div_of_nonneg_right hhalf_lt.le (by positivity))), ?_⟩
  intro F T M _ _ _ _ _ _ _ _ H hrH he hconstant hanalytic Q horn hboundary
  let H' := H.restrictRadius rho hr hrH.le
  let Q' := Q.restrictRadius rho hr hrH.le
  have hden : 0 < 2 * H.constant := mul_pos (by norm_num) H.constant_pos
  have hcut : (rho / 2) / (2 * H.constant) ≤ rho / (2 * H.constant) :=
    div_le_div_of_nonneg_right hhalf_lt.le hden.le
  obtain ⟨D⟩ := hgeom H' rfl he hconstant hanalytic Q' horn
    (hornBoundaryBelow_of_le (div_pos hhalf hden) hcut hboundary)
  exact ⟨deepHornConclusion_mono D H.constant_pos hhalf hhalf_lt.le hd le_rfl⟩

theorem exists_deepHornScaleSelection_of_fixedRadiusIntervals
    {epsilon C analyticConstant : ℝ} (hC : 0 < C)
    (hlocal : ∀ r₀ rho delta : ℝ, 0 < r₀ → 0 < rho → rho < r₀ → 0 < delta →
      ∃ b : ℝ, 0 < b ∧ ∀ a : ℝ, 0 < a → a ≤ b →
        UniformDeepHornHeightAtRadius.{u} epsilon C analyticConstant r₀ rho delta a) :
    Nonempty (M32DeepHornScaleSelection.{u} epsilon C analyticConstant) :=
  exists_deepHornScaleSelection_of_uniformHeight hC
    (uniformHeight_of_restrictRadius hC hlocal)

end PoincareConjecture.M32
