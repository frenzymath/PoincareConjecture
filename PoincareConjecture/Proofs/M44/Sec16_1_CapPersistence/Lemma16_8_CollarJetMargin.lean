import PoincareConjecture.Proofs.M44.Mathlib.SectionalNormalization
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_TwoJetModulus
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareConjecture.Definitions.Ch04.Pinching
import Mathlib.Topology.MetricSpace.Thickening











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 16

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance collarCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance collarCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance collarTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance collarTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace



noncomputable def collarJetGram (u v : E) (J : MetricTwoJet 3) : ℝ :=
  J.1 u u * J.1 v v - (J.1 u v) ^ 2




noncomputable def collarJetMargin (C : ℝ) (u v : E) (J : MetricTwoJet 3) : ℝ :=
  C⁻¹ * jetScalarCurvature J - jetCurvature J u v u v / collarJetGram u v J



def collarJetRegion (C : ℝ) (u v : E) : Set (MetricTwoJet 3) :=
  {J | J.1.IsInvertible ∧ 0 < collarJetGram u v J ∧ 0 < collarJetMargin C u v J}



theorem continuous_collarJetGram (u v : E) : Continuous (collarJetGram u v) := by
  unfold collarJetGram
  fun_prop



theorem continuousAt_collarJetMargin (C : ℝ) (u v : E) {J : MetricTwoJet 3}
    (hJ : J.1.IsInvertible) (hgram : collarJetGram u v J ≠ 0) :
    ContinuousAt (collarJetMargin C u v) J :=
  (continuousAt_const.mul (contDiffAt_jetScalarCurvature hJ).continuousAt).sub
    ((contDiffAt_jetCurvature hJ u v u v).continuousAt.div
      (continuous_collarJetGram u v).continuousAt hgram)



theorem isOpen_collarJetRegion (C : ℝ) (u v : E) : IsOpen (collarJetRegion C u v) := by
  rw [isOpen_iff_mem_nhds]
  intro J hJ
  have hinv := (isOpen_ricciFlowOperator_domain 3).mem_nhds hJ.1
  have hgram := (continuous_collarJetGram u v).continuousAt.eventually
    (lt_mem_nhds hJ.2.1)
  have hmargin := (continuousAt_collarJetMargin C u v hJ.1 hJ.2.1.ne').eventually
    (lt_mem_nhds hJ.2.2)
  filter_upwards [hinv, hgram, hmargin] with J' hI hG hM
  exact ⟨hI, hG, hM⟩

set_option synthInstance.maxHeartbeats 100000 in




theorem exists_uniform_collar_jet_margin (C : ℝ) (u v : E)
    {K : Set (MetricTwoJet 3)} (hK : IsCompact K) (hsub : K ⊆ collarJetRegion C u v) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ J ∈ K, ∀ J' : MetricTwoJet 3,
      ‖J' - J‖ ≤ delta → J' ∈ collarJetRegion C u v := by
  obtain ⟨delta, hdelta, hinside⟩ :=
    hK.exists_cthickening_subset_open (isOpen_collarJetRegion C u v) hsub
  refine ⟨delta, hdelta, ?_⟩
  intro J hJ J' hnear
  apply hinside
  exact Metric.mem_cthickening_of_dist_le J' J delta K hJ (by
    simpa only [dist_eq_norm] using hnear)




theorem exists_collar_plane_of_twoJet
    {g : RiemannianMetric 3 E} (D : LeviCivitaData g) (x : E) (C : ℝ) (u v : E)
    (hJ : metricTwoJet g.euclideanCoefficients x ∈ collarJetRegion C u v) :
    ∃ p q : TangentSpace (𝓡 3) x, LeviCivitaData.IsOrthonormalPair g x p q ∧
      D.sectionalCurvature x p q < C⁻¹ * D.scalarCurvature x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : E → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hgram : 0 < g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 := hJ.2.1
  obtain ⟨p, q, hp, hq, hpq, hvalue⟩ :=
    exists_orthonormal_curvature_quotient (M13.curvatureTensorLinear D x)
      (fun a b c d => D.curvatureTensor_swap_first x a b c d)
      (fun a b c d => D.curvatureTensor_swap_last x a b c d) u v hgram
  change g.inner x p p = 1 at hp
  change g.inner x q q = 1 at hq
  change g.inner x p q = 0 at hpq
  change D.curvatureTensor x p q p q = D.sectionalCurvature x u v at hvalue
  have hmargin : D.sectionalCurvature x u v < C⁻¹ * D.scalarCurvature x := by
    have h := hJ.2.2
    simp only [collarJetMargin, jetScalarCurvature_metricTwoJet D,
      jetCurvature_metricTwoJet D] at h
    exact sub_pos.mp h
  refine ⟨p, q, ⟨hp, hq, hpq⟩, ?_⟩
  calc
    D.sectionalCurvature x p q = D.curvatureTensor x p q p q := by
      simp only [LeviCivitaData.sectionalCurvature, hp, hq, hpq, one_mul,
        zero_pow (by decide : 2 ≠ 0), sub_zero, div_one]
    _ = D.sectionalCurvature x u v := hvalue
    _ < C⁻¹ * D.scalarCurvature x := hmargin

set_option synthInstance.maxHeartbeats 100000 in




theorem exists_collar_jet_time_margin (C : ℝ) (u v : E)
    {K : Set (MetricTwoJet 3)} (hK : IsCompact K) (hsub : K ⊆ collarJetRegion C u v)
    {L : ℝ} (hL : 0 ≤ L) :
    ∃ delta tau : ℝ, 0 < delta ∧ 0 < tau ∧
      ∀ (B : ℝ → E → MetricCoefficient 3) (x : E) (J : MetricTwoJet 3), J ∈ K →
      ‖metricTwoJet (B 0) x - J‖ ≤ delta →
      ∀ t : ℝ, 0 ≤ t → t ≤ tau →
      (∀ j ≤ 2, ‖iteratedFDeriv ℝ j (B t) x - iteratedFDeriv ℝ j (B 0) x‖ ≤ L * t) →
        metricTwoJet (B t) x ∈ collarJetRegion C u v := by
  obtain ⟨d, hd, hmargin⟩ := exists_uniform_collar_jet_margin C u v hK hsub
  let tau := (d / 3) / (L + 1)
  have hden : 0 < L + 1 := by linarith only [hL]
  have htau : 0 < tau := div_pos (by positivity) hden
  have hLt : L * tau ≤ d / 3 := by
    calc
      _ ≤ (L + 1) * tau := mul_le_mul_of_nonneg_right (by linarith) htau.le
      _ = d / 3 := by dsimp [tau]; field_simp
  refine ⟨d / 3, tau, by positivity, htau, ?_⟩
  intro B x J hJ hinitial t _ht htime hjets
  apply hmargin J hJ _
  calc
    _ ≤ ‖metricTwoJet (B t) x - metricTwoJet (B 0) x‖ +
        ‖metricTwoJet (B 0) x - J‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ L * t + d / 3 := add_le_add (norm_metricTwoJet_sub_le _ _ _ hjets) hinitial
    _ ≤ L * tau + d / 3 := add_le_add (mul_le_mul_of_nonneg_left htime hL) le_rfl
    _ ≤ d := by linarith only [hLt, hd]

end PoincareConjecture.M44
