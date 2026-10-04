import PoincareLib.Geometry.RicciFlow.Surgery.Singular.Limit

/-!
Adapted from Mapher `PoincareMT/Definitions/M32HornSelection.lean` at
`0bf00434d6783c9fed79b6a8fa3a8349cfc78335`. Declaration bodies are retained;
see `references/ricci-flow/mapher/terminal-accuracy-contract.json`.
-/

/-!
# M32 repaired strong-neck and deep-horn selection data

The output is attached to the actual singular-limit extension. Corollary
11.36 also supplies one monotone height function whose geometric conclusion
holds on that same extension, including at smaller positive heights.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- The numerical height function reused by Definition 15.5. Its geometric
validity is a separate M32 conclusion, not a property of every such function. -/
structure CommonSurgeryScaleSelector where
  h : ℝ → ℝ → ℝ
  h_pos : ∀ rho delta, 0 < rho → 0 < delta → 0 < h rho delta
  h_le : ∀ rho delta, 0 < rho → 0 < delta → h rho delta ≤ rho * delta
  h_mono_rho : ∀ delta, 0 ≤ delta →
    MonotoneOn (fun rho => h rho delta) (Set.Ici 0)
  h_mono_delta : ∀ rho, 0 ≤ rho → MonotoneOn (h rho) (Set.Ici 0)

/-- Theorem 11.31 and Corollary 11.36, after rethresholding the same limit.
The chosen function depends on both the geometric and analytic constants,
and is uniform in the original canonical radius and in all flows, reference
manifolds, limits and horns. -/
structure M32DeepHornScaleSelection (epsilon C analyticConstant : ℝ)
    extends CommonSurgeryScaleSelector where
  h_upper : ∀ rho delta, 0 < rho → 0 < delta → h rho delta ≤ rho / (2 * C)
  deep_horn : ∀ rho delta a : ℝ,
    0 < rho → 0 < delta → 0 < a → a ≤ h rho delta →
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

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]

/-- Horn output attached to one repaired singular-limit conclusion. -/
structure RepairedHornSelectionData
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (H : SingularTimeAssumptions F T M) where
  limit : SingularLimitConclusion H

/-- Decreasing the canonical radius only raises the scalar threshold at
which the existing controls are required. The flow and reference stay fixed. -/
def SingularTimeAssumptions.restrictRadius
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    (H : SingularTimeAssumptions F T M) (r : ℝ)
    (hr : 0 < r) (hle : r ≤ H.r₀) : SingularTimeAssumptions F T M := by
  have hthreshold : H.r₀⁻¹ ^ 2 ≤ r⁻¹ ^ 2 := by
    exact pow_le_pow_left₀ (inv_nonneg.mpr H.r₀_pos.le)
      ((inv_le_inv₀ H.r₀_pos hr).2 hle) 2
  exact { H with
    r₀ := r
    r₀_pos := hr
    scalar_time_derivative_bound := fun b t ht x hx =>
      H.scalar_time_derivative_bound b t ht x (hthreshold.trans hx)
    scalar_gradient_bound := fun t ht x hx =>
      H.scalar_gradient_bound t ht x (hthreshold.trans hx)
    canonical_control := fun t ht hregular x hx =>
      H.canonical_control t ht hregular x (hthreshold.trans hx) }

/-- The radius restriction retains literally the same terminal extension,
metric and end data; only the canonical-threshold proof changes. -/
def SingularLimitConclusion.restrictRadius
    {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
    {H : SingularTimeAssumptions F T M}
    (Q : SingularLimitConclusion H) (r : ℝ)
    (hr : 0 < r) (hle : r ≤ H.r₀) :
    SingularLimitConclusion (H.restrictRadius r hr hle) := by
  have hthreshold : H.r₀⁻¹ ^ 2 ≤ r⁻¹ ^ 2 := by
    exact pow_le_pow_left₀ (inv_nonneg.mpr H.r₀_pos.le)
      ((inv_le_inv₀ H.r₀_pos hr).2 hle) 2
  exact { Q with
    canonical_neighborhood := fun x hx =>
      Q.canonical_neighborhood x (hthreshold.trans_lt hx) }

end PoincareMT
