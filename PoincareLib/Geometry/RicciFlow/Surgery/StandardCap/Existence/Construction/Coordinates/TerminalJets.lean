import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Coordinates.PartialFlowJetLimits
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Coordinates.CompactUniformJetLimits

/-!
# Compatible smooth terminal metric coefficients

Choose all terminal spatial jets by their full left limits. The
compact-uniform time modulus identifies them as the derivatives of one
smooth coefficient field. This supplies the spatial terminal metric for
Morgan-Tian Theorem 12.5, pp. 296-297; see terminal-coefficient-limit.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Terminal jets take values in iterated multilinear-map spaces.
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace PoincareMT.M34

open SpacetimeBounds

/-- All actual spatial metric jets with their full left-limit witnesses
at a fixed terminal time (Theorem 12.5, pp. 296-297). -/
structure PartialFlowTerminalJets {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) (S : ℝ) where
  /-- The order-m coefficient jet at each spatial point. -/
  jet : (m : ℕ) → StandardCapSpace → StandardCapSpace [×m]→L[ℝ] MetricCoefficient 3
  /-- Each selected jet is the full limit of the actual old spatial jet. -/
  jet_tendsto : ∀ m x,
    Tendsto (fun t => iteratedFDeriv ℝ m (F.flow.metric t).euclideanCoefficients x)
      (𝓝[<] S) (𝓝 (jet m x))

/-- A finite bounded-curvature horizon admits terminal jets of every
spatial order (Theorem 12.5, pp. 296-297). -/
theorem partialFlowTerminalJets_nonempty (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : PartialStandardCapFlow g0) {S B : ℝ} (hS : 0 < S)
    (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B) :
    Nonempty (PartialFlowTerminalJets F S) := by
  classical
  choose J hJ using partialFlow_spatialJet_terminal_limit_exists P E0 F hS hSF hB hfull
  exact ⟨⟨J, hJ⟩⟩

namespace PartialFlowTerminalJets

variable {g0 : StandardInitialMetric} {F : PartialStandardCapFlow g0} {S : ℝ}
  (L : PartialFlowTerminalJets F S)

/-- The same compact-uniform Lipschitz constants control the error to
the selected terminal jets (Theorem 12.5, pp. 296-297). -/
theorem exists_compact_terminal_modulus (P : RicciFlowCurvatureTheory.{0})
    (E0 : StandardCapEstimate g0) {B : ℝ} (hS : 0 < S)
    (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B)
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Ico 0 S, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ m (F.flow.metric t).euclideanCoefficients x - L.jet m x‖ ≤
        D * (S - t) := by
  obtain ⟨D, hD⟩ := partialFlow_compact_spatialJet_time_lipschitz
    P E0 F hS hSF hB hfull hK m
  refine ⟨D, D.coe_nonneg, ?_⟩
  intro t ht x hx
  obtain ⟨z, hz, hmod⟩ := (hD x hx).exists_terminal_limit hS
  have heq : z = L.jet m x := tendsto_nhds_unique hz (L.jet_tendsto m x)
  simpa only [heq] using hmod t ht

/-- Every spatial jet converges uniformly on every compact spatial set
to its terminal value (Theorem 12.5, pp. 296-297). -/
theorem tendstoUniformlyOn_jet (P : RicciFlowCurvatureTheory.{0})
    (E0 : StandardCapEstimate g0) {B : ℝ} (hS : 0 < S)
    (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B)
    (m : ℕ) {K : Set StandardCapSpace} (hK : IsCompact K) :
    TendstoUniformlyOn (fun t => iteratedFDeriv ℝ m (F.flow.metric t).euclideanCoefficients)
      (L.jet m) (𝓝[<] S) K := by
  obtain ⟨D, _hD, hmod⟩ := L.exists_compact_terminal_modulus P E0 hS hSF hB hfull hK m
  exact tendstoUniformlyOn_of_terminal_norm_bound hS hmod

/-- The zeroth terminal jet, viewed as an actual bilinear coefficient
field (Theorem 12.5, pp. 296-297). -/
noncomputable def coefficients (x : StandardCapSpace) : MetricCoefficient 3 :=
  (L.jet 0 x).curry0

/-- The chosen terminal jets satisfy the actual all-order Taylor
compatibility predicate (Theorem 12.5, pp. 296-297). -/
theorem hasFTaylorSeriesUpTo (P : RicciFlowCurvatureTheory.{0})
    (E0 : StandardCapEstimate g0) {B : ℝ} (hS : 0 < S)
    (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B) :
    HasFTaylorSeriesUpTo ∞ L.coefficients (fun x m => L.jet m x) := by
  apply hasFTaylorSeriesUpTo_of_compact_uniform_jet_limits (𝕜 := ℝ)
    (f := fun t => (F.flow.metric t).euclideanCoefficients)
    (p := fun x m => L.jet m x) (l := 𝓝[<] S)
  · intro t
    exact contDiff_iff_contDiffAt.mpr (F.flow.metric t).contDiffAt_euclideanCoefficients
  · exact fun m _K hK => L.tendstoUniformlyOn_jet P E0 hS hSF hB hfull m hK

/-- The terminal bilinear coefficient field is smooth on the entire
original cap space (Theorem 12.5, pp. 296-297). -/
theorem contDiff_coefficients (P : RicciFlowCurvatureTheory.{0})
    (E0 : StandardCapEstimate g0) {B : ℝ} (hS : 0 < S)
    (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B) :
    ContDiff ℝ ∞ L.coefficients :=
  (L.hasFTaylorSeriesUpTo P E0 hS hSF hB hfull).contDiff

/-- Each selected terminal jet equals the actual derivative of the
terminal coefficient field (Theorem 12.5, pp. 296-297). -/
theorem jet_eq_iteratedFDeriv (P : RicciFlowCurvatureTheory.{0})
    (E0 : StandardCapEstimate g0) {B : ℝ} (hS : 0 < S)
    (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B)
    (m : ℕ) (x : StandardCapSpace) :
    L.jet m x = iteratedFDeriv ℝ m L.coefficients x :=
  (L.hasFTaylorSeriesUpTo P E0 hS hSF hB hfull).eq_iteratedFDeriv
    (by exact_mod_cast le_top) x

end PartialFlowTerminalJets
end PoincareMT.M34
