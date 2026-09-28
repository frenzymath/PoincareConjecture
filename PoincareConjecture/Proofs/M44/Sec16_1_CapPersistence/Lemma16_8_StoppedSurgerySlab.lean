import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_StoppedCollar
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_NormalizedSlabBound











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance surgerySlabCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance surgerySlabCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance surgerySlabTwoJetNormedGroup :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance surgerySlabTwoJetNormedSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace




theorem exists_stopped_surgery_slab_bound (P : M44CapPersistencePredecessors.{u})
    (C : ℝ) (u v : E) {model : Set (MetricTwoJet 3)} (hmodel : IsCompact model)
    (hmargin : model ⊆ collarJetRegion C u v)
    {M K0 H r alpha beta Z : ℝ} (hM : 0 < M) (hK0 : 0 < K0)
    (hH : 0 < H) (hr : 0 < r) (halpha : 0 < alpha) (hbeta : 0 ≤ beta) (hZ : 1 ≤ Z) :
    ∃ delta tau : ℝ, 0 < delta ∧ 0 < tau ∧
      ∀ (F : SurgeryFlowData.{u}) {origin T sigma : ℝ},
      0 < T → T ≤ H → T ≤ tau → 0 < sigma → sigma ≤ 1 →
      ∀ (S : SurgeryRegularSlab F.slice F.metric origin (origin + T * sigma))
        (G : RicciFlow 3 (F.slice origin).carrier (Icc 0 T)),
      (∀ s ∈ Icc (0 : ℝ) T, ∀ y w z,
        (S.flow.metric (origin + s * sigma)).inner y w z =
          sigma * (G.metric s).inner y w z) →
      ∀ e : PartialDiffeomorph (𝓡 3) (𝓡 3) E (F.slice origin).carrier ∞,
      IsPreconnected e.target →
      (∀ j ≤ 2, ∀ y ∈ e.target, (G.connection 0).curvatureDerivativeNorm j y ≤ K0) →
      (∀ y ∈ e.target, (G.connection 0).scalarCurvature y ≤ M) →
      ∀ {q : ℝ}, sigma * q ≤ M →
      (∀ t : Ico origin (origin + T * sigma), ∀ y ∈ e.target,
        q ≤ (S.flow.connection t.1).scalarCurvature y →
        SurgeryCanonicalControl F t.1 (S.identify ⟨t.1, t.2.1, t.2.2.le⟩ y)
          F.parameters.epsilon C) →
      SurgeryFlowPinched F → Icc origin (origin + T * sigma) ⊆ F.time_domain →
      ∀ {V : Set E}, IsOpen V → V ⊆ e.source →
      (∀ y ∈ V, IsCompact (closure ((G.metric 0).ball (e y) r))) →
      (∀ y ∈ V, closure ((G.metric 0).ball (e y) r) ⊆ e.target) →
      (∀ y ∈ V, ∀ w, alpha * ‖w‖ ^ 2 ≤ (G.metric 0).pullbackCoefficients e y w w) →
      (∀ y ∈ V, ∀ w, (G.metric 0).pullbackCoefficients e y w w ≤ beta * ‖w‖ ^ 2) →
      (∀ y ∈ V, ∀ j ≤ 2,
        ‖iteratedFDeriv ℝ j ((G.metric 0).pullbackCoefficients e) y‖ ≤ Z) →
      ∀ x ∈ V, ∀ J ∈ model,
      ‖metricTwoJet ((G.metric 0).pullbackCoefficients e) x - J‖ ≤ delta →
      (∀ s ∈ Icc (0 : ℝ) T,
        metricTwoJet ((G.metric s).pullbackCoefficients e) x ∈ collarJetRegion C u v) ∧
      (∀ s ∈ Icc (0 : ℝ) T, ∀ y ∈ e.target,
        (G.connection s).scalarCurvature y ≤ 2 * M ∧
        (G.connection s).curvatureTensorNorm y ≤ 13 * max (2 * M) (Real.exp 4)) := by
  obtain ⟨L, hL, hbound⟩ := exists_normalized_slab_curvature_bound P C
  let K := max K0 (13 * max (2 * M) (Real.exp 4)) + 1
  have hK0K : K0 ≤ K := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hBK : 13 * max (2 * M) (Real.exp 4) ≤ K :=
    (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hK : 0 < K := hK0.trans_le hK0K
  obtain ⟨delta, tau, hdelta, htau, hstop⟩ :=
    exists_stopped_local_collar P C u v hmodel hmargin hK hH hr halpha hbeta hZ
  have hden : 0 < 8 * L * M := by positivity
  refine ⟨delta, min tau (1 / (8 * L * M)), hdelta,
    lt_min htau (div_pos zero_lt_one hden), ?_⟩
  intro F origin T sigma hT hTH hTtau hsigma hsmall S G hmetric e hconnected
    hinitial hinitialScalar q hq hcanonical hpinch hdomain V hV hsub hcompact hinside
    hlower hupper hjets x hx J hJ hnear
  have hshort : 8 * L * M * T ≤ 1 := by
    have h := (le_div_iff₀ hden).mp (hTtau.trans (min_le_right _ _))
    simpa only [mul_comm] using h
  have hcontrolled (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) T)
      (hprior : ∀ s ∈ Ico (0 : ℝ) c, ∃ p q : TangentSpace (𝓡 3) (e x),
        LeviCivitaData.IsOrthonormalPair (G.metric s) (e x) p q ∧
        (G.connection s).sectionalCurvature (e x) p q <
          C⁻¹ * (G.connection s).scalarCurvature (e x)) :
      ∀ s ∈ Icc (0 : ℝ) c, ∀ y ∈ e.target, (G.connection s).curvatureTensorNorm y ≤ K := by
    have hac : origin < origin + c * sigma := lt_add_of_pos_right _ (mul_pos hc.1 hsigma)
    have hright : origin + c * sigma ≤ origin + T * sigma := by
      linarith only [mul_le_mul_of_nonneg_right hc.2 hsigma.le]
    let Sc := restrictRegularSlabRight S hac hright
    let Gc := Poincare.Geometry.RicciFlow.Harnack.restrictFlow G
      (Icc_subset_Icc le_rfl hc.2) ordConnected_Icc
      (show (Icc (0 : ℝ) c).Nontrivial from
        ⟨0, ⟨le_rfl, hc.1.le⟩, c, ⟨hc.1.le, le_rfl⟩, hc.1.ne⟩)
    have hmetric' (s : ℝ) (hs : s ∈ Icc (0 : ℝ) c) (y w z) :
        (Sc.flow.metric (origin + s * sigma)).inner y w z =
          sigma * (Gc.metric s).inner y w z :=
      hmetric s ⟨hs.1, hs.2.trans hc.2⟩ y w z
    have hcanonical' (t : Ico origin (origin + c * sigma)) (y) (hy : y ∈ e.target)
        (hhigh : q ≤ (Sc.flow.connection t.1).scalarCurvature y) :
        SurgeryCanonicalControl F t.1 (Sc.identify ⟨t.1, t.2.1, t.2.2.le⟩ y)
          F.parameters.epsilon C :=
      hcanonical ⟨t.1, t.2.1, t.2.2.trans_le hright⟩ y hy hhigh
    have hshort' : 8 * L * M * c ≤ 1 :=
      (mul_le_mul_of_nonneg_left hc.2 hden.le).trans hshort
    have hdomain' : Icc origin (origin + c * sigma) ⊆ F.time_domain :=
      (Icc_subset_Icc le_rfl hright).trans hdomain
    have hb := hbound F hc.1 hsigma hsmall Sc Gc hmetric' e.target hconnected (e x)
      (e.map_source (hsub hx)) hM hq hcanonical' hinitialScalar hprior hshort' hpinch hdomain'
    intro s hs y hy
    exact (hb s hs y hy).2.trans hBK
  obtain ⟨hkeep, _hcurvature⟩ := hstop (F.slice origin).carrier hT hTH
    (hTtau.trans (min_le_left _ _)) G e
    (fun j hj y hy => (hinitial j hj y hy).trans hK0K)
    hV hsub hcompact hinside hlower hupper hjets x hx J hJ hnear hcontrolled
  refine ⟨hkeep, ?_⟩
  apply hbound F hT hsigma hsmall S G hmetric e.target hconnected (e x)
    (e.map_source (hsub hx)) hM hq hcanonical hinitialScalar _ hshort hpinch hdomain
  intro s hs
  apply exists_collar_plane_of_pullback_twoJet (G.metric s) (G.connection s)
    e.open_source e.contMDiffOn _ (hsub hx) C u v (hkeep s ⟨hs.1, hs.2.le⟩)
  intro y hy
  exact ⟨(e.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hy).mfderivToContinuousLinearEquiv
    (by simp), rfl⟩

end PoincareConjecture.M44
