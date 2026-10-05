import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Comparison.Evolution.StandardIdentification
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Comparison.Evolution.FamilyJetsBounds

/-!
# Uniqueness turns subsequential jet limits into uniform comparison

On each fixed slab strictly before the limiting lifetime, compactness
can be applied on a slightly larger slab. M35 identifies every such
partial limit with the same standard model. Thus the full sequence
converges on the fixed slab, which is the interior input for the moving
endpoint argument. Morgan--Tian, Corollary 16.9, p. 373;
M44 derivation 81.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareMT.M44

local notation "E" => StandardCapSpace
local notation "V" => E →L[ℝ] E →L[ℝ] ℝ

noncomputable local instance familyConvergenceCoefficientNorm : NormedAddCommGroup V :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance familyConvergenceCoefficientSpace : NormedSpace ℝ V :=
  ContinuousLinearMap.toNormedSpace

/-- If every subsequence has a further uniformly convergent subsequence
with the same target, uniform convergence holds for the full sequence.
Source: the compactness contradiction in Corollary 16.9; derivation 81. -/
theorem tendstoUniformlyOn_of_subsubsequence
    {X Y : Type*} [PseudoMetricSpace Y] {f : ℕ → X → Y} {g : X → Y} {K : Set X}
    (hsub : ∀ sigma : ℕ → ℕ, StrictMono sigma →
      ∃ tau : ℕ → ℕ, StrictMono tau ∧
        TendstoUniformlyOn (fun n => f (sigma (tau n))) g atTop K) :
    TendstoUniformlyOn f g atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  by_contra hnot
  obtain ⟨sigma, hsigma, hbad⟩ :=
    extraction_of_frequently_atTop (not_eventually.mp hnot)
  obtain ⟨tau, _, hconv⟩ := hsub sigma hsigma
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hconv epsilon hepsilon).exists
  exact hbad (tau n) hn

/-- M35 identifies all spatial jets of the actual partial limit on the
common time domain with the chosen maximal model. Source: Corollary
16.9, p. 373; derivation 81. -/
theorem tendstoUniformlyOn_partial_spatialJets_model
    {g0 : StandardInitialMetric} {E0 : RepairedStandardCapExistenceData g0}
    (U : RepairedStandardCapUniquenessData g0 E0)
    (G : PartialStandardCapFlow g0) (S : MaximalStandardCapFlow g0)
    (m : ℕ)
    {f : ℕ → ℝ × StandardCapSpace →
      StandardCapSpace [×m]→L[ℝ] (StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ)}
    {K : Set (ℝ × StandardCapSpace)}
    (htime : ∀ p ∈ K, p.1 ∈ Ico (0 : ℝ) 1 ∧ p.1 < G.lifetime)
    (hconv : TendstoUniformlyOn f
      (fun p => iteratedFDeriv ℝ m (G.flow.metric p.1).euclideanCoefficients p.2)
      atTop K) :
    TendstoUniformlyOn f
      (fun p => iteratedFDeriv ℝ m (S.metric p.1).euclideanCoefficients p.2) atTop K := by
  apply hconv.congr_right
  intro p hp
  dsimp only
  rw [U.partial_metric_eq_model G S (htime p hp).1 (htime p hp).2]

end PoincareMT.M44
