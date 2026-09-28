import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_StoppedCollarRestart
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CylinderScalarRestart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance restartCylinderCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance restartCylinderCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

noncomputable local instance restartCylinderTwoJetNorm :
    NormedAddCommGroup (MetricTwoJet 3) := Prod.normedAddCommGroup

noncomputable local instance restartCylinderTwoJetSpace :
    NormedSpace ℝ (MetricTwoJet 3) := Prod.normedSpace

theorem exists_stopped_cylinder_restart_bound (P : M44CapPersistencePredecessors.{u})
    (C0 : ℝ) (u v : E) {model : Set (MetricTwoJet 3)} (hmodel : IsCompact model)
    (hmargin : model ⊆ collarJetRegion C0 u v)
    {M K0 Kpast H r alpha beta Z : ℝ} (hM : 0 < M) (hK0 : 0 < K0)
    (hH : 0 < H) (hr : 0 < r) (halpha : 0 < alpha) (hbeta : 0 ≤ beta) (hZ : 1 ≤ Z) :
    ∃ delta tau : ℝ, 0 < delta ∧ 0 < tau ∧
      ∀ (F : SurgeryFlowData.{u}) (C : GeneralizedSliceCarrier.{u})
        {origin scale B a T : ℝ} {U : Set C.carrier}
        (e : SurgeryFlowCylinder F C origin scale (Ico 0 B) U),
      IsOpen U → scale⁻¹ ≤ 1 →
      ∀ f : PartialDiffeomorph (𝓡 3) (𝓡 3) E C.carrier ∞,
      f.target ⊆ U → IsPreconnected f.target →
      ∀ G : CylinderRicciFlow e f, 0 ≤ a → a < T → T < B → T ≤ H → T - a ≤ tau →
      ∀ {q : ℝ}, q ≤ M →
      (∀ s ∈ Ico a T, ∀ y : (⟨f.target, f.open_target⟩ : Opens C.carrier),
        q ≤ (G.flow.connection s).scalarCurvature y →
        ∀ hs : s ∈ Ico 0 B,
          SurgeryCanonicalControl F (origin + s / scale) (cylinderTargetTransport e f s hs y)
            F.parameters.epsilon C0) →
      (∀ y, (G.flow.connection a).scalarCurvature y ≤ M) →
      (∀ s ∈ Icc (0 : ℝ) a, ∀ y, (G.flow.connection s).curvatureTensorNorm y ≤ Kpast) →
      SurgeryFlowPinched F →
      ∀ chart : PartialDiffeomorph (𝓡 3) (𝓡 3) E
        (⟨f.target, f.open_target⟩ : Opens C.carrier) ∞,
      (∀ j ≤ 2, ∀ y ∈ chart.target,
        (G.flow.connection 0).curvatureDerivativeNorm j y ≤ K0) →
      ∀ {V : Set E}, IsOpen V → V ⊆ chart.source →
      (∀ y ∈ V, IsCompact (closure ((G.flow.metric 0).ball (chart y) r))) →
      (∀ y ∈ V, closure ((G.flow.metric 0).ball (chart y) r) ⊆ chart.target) →
      (∀ y ∈ V, ∀ w,
        alpha * ‖w‖ ^ 2 ≤ (G.flow.metric 0).pullbackCoefficients chart y w w) →
      (∀ y ∈ V, ∀ w,
        (G.flow.metric 0).pullbackCoefficients chart y w w ≤ beta * ‖w‖ ^ 2) →
      (∀ y ∈ V, ∀ j ≤ 2,
        ‖iteratedFDeriv ℝ j ((G.flow.metric 0).pullbackCoefficients chart) y‖ ≤ Z) →
      ∀ x ∈ V, ∀ J ∈ model,
      ‖metricTwoJet ((G.flow.metric a).pullbackCoefficients chart) x - J‖ ≤ delta →
      (∀ s ∈ Icc a T,
        metricTwoJet ((G.flow.metric s).pullbackCoefficients chart) x ∈
          collarJetRegion C0 u v) ∧
      (∀ s ∈ Icc a T, ∀ y,
        (G.flow.connection s).scalarCurvature y ≤ 2 * M ∧
        (G.flow.connection s).curvatureTensorNorm y ≤ 13 * max (2 * M) (Real.exp 4)) := by
  obtain ⟨L, hL, hbound⟩ := exists_cylinder_curvature_restart_constant P C0
  let K1 := max Kpast (max K0 (13 * max (2 * M) (Real.exp 4))) + 1
  have hpastK : Kpast ≤ K1 :=
    (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hK0K : K0 ≤ K1 :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_add_of_nonneg_right zero_le_one)
  have hBK : 13 * max (2 * M) (Real.exp 4) ≤ K1 :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_add_of_nonneg_right zero_le_one)
  obtain ⟨delta, tau, hdelta, htau, hstop⟩ :=
    exists_stopped_local_collar_restart P C0 u v hmodel hmargin
      (hK0.trans_le hK0K) hH hr halpha hbeta hZ
  have hden : 0 < 8 * L * M := by positivity
  refine ⟨delta, min tau (1 / (8 * L * M)), hdelta,
    lt_min htau (div_pos zero_lt_one hden), ?_⟩
  intro F C origin scale B a T U e hU hsmall f hmap hconnected G ha haT hTB hTH hTtau
    q hq hcanonical hscalar hpast hpinch chart hinitial V hV hsub hcompact hinside
    hlower hupper hjets x hx J hJ hnear
  have hshort : 8 * L * M * (T - a) ≤ 1 := by
    have h := (le_div_iff₀ hden).mp (hTtau.trans (min_le_right _ _))
    simpa only [mul_comm] using h
  let Gc := Poincare.Geometry.RicciFlow.Harnack.restrictFlow G.flow
    (show Icc (0 : ℝ) T ⊆ Ico 0 B from fun _ hs => ⟨hs.1, hs.2.trans_lt hTB⟩)
    ordConnected_Icc (Icc_infinite (ha.trans_lt haT)).nontrivial
  have hcontrolled (c : ℝ) (hc : c ∈ Ioc a T)
      (hprior : ∀ s ∈ Ico a c, ∃ p q : TangentSpace (𝓡 3) (chart x),
        LeviCivitaData.IsOrthonormalPair (Gc.metric s) (chart x) p q ∧
        (Gc.connection s).sectionalCurvature (chart x) p q <
          C0⁻¹ * (Gc.connection s).scalarCurvature (chart x)) :
      ∀ s ∈ Icc (0 : ℝ) c, ∀ y ∈ chart.target,
        (Gc.connection s).curvatureTensorNorm y ≤ K1 := by
    have hb := hbound F C e hU hsmall f hmap hconnected G ha hc.1
      (hc.2.trans_lt hTB) hM hq
      (fun s hs y hhigh hsI => hcanonical s ⟨hs.1, hs.2.trans_le hc.2⟩ y hhigh hsI)
      hscalar (fun s hs => by
        obtain ⟨p, q, horth, hplane⟩ := hprior s hs
        exact ⟨chart x, p, q, horth, hplane⟩)
      ((mul_le_mul_of_nonneg_left (sub_le_sub_right hc.2 a) hden.le).trans hshort) hpinch
    intro s hs y _hy
    rcases le_total s a with hsa | has
    · exact (hpast s ⟨hs.1, hsa⟩ y).trans hpastK
    · exact (hb s ⟨has, hs.2⟩ y).2.trans hBK
  obtain ⟨hkeep, _⟩ := hstop (⟨f.target, f.open_target⟩ : Opens C.carrier)
    ha haT hTH (hTtau.trans (min_le_left _ _)) Gc chart
    (fun j hj y hy => (hinitial j hj y hy).trans hK0K) hV hsub hcompact hinside
    hlower hupper hjets x hx J hJ hnear hcontrolled
  refine ⟨hkeep, ?_⟩
  apply hbound F C e hU hsmall f hmap hconnected G ha haT hTB hM hq hcanonical hscalar
    _ hshort hpinch
  intro s hs
  refine ⟨chart x, ?_⟩
  apply exists_collar_plane_of_pullback_twoJet (G.flow.metric s) (G.flow.connection s)
    chart.open_source chart.contMDiffOn _ (hsub hx) C0 u v (hkeep s ⟨hs.1, hs.2.le⟩)
  intro y hy
  exact ⟨(chart.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hy).mfderivToContinuousLinearEquiv
    (by simp), rfl⟩

end PoincareConjecture.M44
