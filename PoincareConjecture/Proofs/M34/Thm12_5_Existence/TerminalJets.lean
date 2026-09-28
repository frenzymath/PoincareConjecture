import PoincareConjecture.Proofs.M34.Thm12_5_Existence.PartialFlowJetLimits
import PoincareConjecture.Proofs.M34.Mathlib.CompactUniformJetLimits










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.M34

open SpacetimeBounds



structure PartialFlowTerminalJets {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) (S : ℝ) where

  jet : (m : ℕ) → StandardCapSpace → StandardCapSpace [×m]→L[ℝ] MetricCoefficient 3

  jet_tendsto : ∀ m x,
    Tendsto (fun t => iteratedFDeriv ℝ m (F.flow.metric t).euclideanCoefficients x)
      (𝓝[<] S) (𝓝 (jet m x))



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



noncomputable def coefficients (x : StandardCapSpace) : MetricCoefficient 3 :=
  (L.jet 0 x).curry0



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



theorem contDiff_coefficients (P : RicciFlowCurvatureTheory.{0})
    (E0 : StandardCapEstimate g0) {B : ℝ} (hS : 0 < S)
    (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B) :
    ContDiff ℝ ∞ L.coefficients :=
  (L.hasFTaylorSeriesUpTo P E0 hS hSF hB hfull).contDiff



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
end PoincareConjecture.M34
