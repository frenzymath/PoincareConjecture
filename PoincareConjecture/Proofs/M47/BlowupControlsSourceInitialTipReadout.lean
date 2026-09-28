import PoincareConjecture.Proofs.M47.BlowupControlsCapSliceMap
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RicciJetNorm
import PoincareConjecture.Proofs.M13.ContractionTransport










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open SpacetimeBounds Proofs.M46

local notation "E" => StandardCapSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

noncomputable local instance tipReadoutCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance tipReadoutCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace



theorem source_capComparison_ricci_lower
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count} {A : ℝ}
    {S : MaximalStandardCapFlow F.standard_initial} {eta : ℝ}
    {J : Set ℝ} {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hh : 0 < F.parameters.h t) (s : ℝ) (hs : s ∈ J)
    {x : E} (hx : x ∈ F.standard_initial.metric.ball 0 A) {mu : ℝ}
    (hlower : ∀ v : E, mu * capComparisonCoefficients e initial.chart s hs x v v ≤
      M44.jetRicciBilinear (metricTwoJet (capComparisonCoefficients e initial.chart s hs) x) v v)
    (w : TangentSpace (𝓡 3) (e.forward s hs (initial.chart x))) :
    (mu / (F.parameters.h t) ^ 2) *
        (F.metric (t + s / ((F.parameters.h t)⁻¹ ^ 2))).inner
          (e.forward s hs (initial.chart x)) w w ≤
      (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).ricci
        (e.forward s hs (initial.chart x)) w w := by
  let Q := (F.parameters.h t)⁻¹ ^ 2
  have hQ : 0 < Q := sq_pos_of_pos (inv_pos.mpr hh)
  let g := F.metric (t + s / Q)
  let D := F.connection (t + s / Q)
  let gQ := m01RescaledMetric g Q hQ
  let DQ := m01RescaledMetric_connection g D Q hQ
  let f := actualCapSliceChart e initial comparison s hs
  have hxsource : x ∈ f.source := by
    rwa [actualCapSliceChart_source]
  have hinv (y : E) (hy : y ∈ f.source) :
      (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible :=
    ⟨(f.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hy).mfderivToContinuousLinearEquiv
      (by simp), rfl⟩
  obtain ⟨gE, DE, V, hV, hxV, hVU, hmetric⟩ :=
    gQ.exists_local_immersive_pullback_realization f f.open_source hxsource
      f.contMDiffOn (fun y hy => (hinv y hy).injective)
  have hgerm : gE.euclideanCoefficients =ᶠ[𝓝 x]
      capComparisonCoefficients e initial.chart s hs := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    have hysource : y ∈ F.standard_initial.metric.ball 0 A := by
      have h := hVU hy
      rwa [actualCapSliceChart_source] at h
    exact (congrArg (fun B : MetricCoefficient 3 => B a b) (hmetric y hy)).trans
      (actualCapSliceChart_metric e initial comparison s hs hh hysource a b)
  have hlocal (v : E) : mu * gE.inner x v v ≤ DE.ricci x v v := by
    have h := hlower v
    rw [← metricTwoJet_congr_of_eventuallyEq hgerm,
      M44.jetRicciBilinear_metricTwoJet DE, ← hgerm.self_of_nhds] at h
    exact h
  have hslots (y : E) (hy : y ∈ V) (a b : E) :
      gE.inner y a b = gQ.inner (f y)
        (mfderiv (𝓡 3) (𝓡 3) f y a) (mfderiv (𝓡 3) (𝓡 3) f y b) :=
    congrArg (fun B : MetricCoefficient 3 => B a b) (hmetric y hy)
  have hhom : MetricHomothety g gQ
      (Diffeomorph.refl (𝓡 3) (F.slice (t + s / Q)).carrier ∞) Q := by
    intro y a b
    simp only [Diffeomorph.coe_refl, mfderiv_id]
    rfl
  have hscale (y : (F.slice (t + s / Q)).carrier)
      (a b : TangentSpace (𝓡 3) y) : DQ.ricci y a b = D.ricci y a b := by
    simpa only [Diffeomorph.coe_refl, mfderiv_id, ContinuousLinearMap.id_apply, id_eq] using
      M13.homothety_ricci_eq g gQ
        (Diffeomorph.refl (𝓡 3) (F.slice (t + s / Q)).carrier ∞) Q hQ hhom D DQ y a b
  obtain ⟨v, hv⟩ := (hinv x hxsource).surjective w
  have hricci := DE.ricci_eq_of_local_isometry DQ hV (f.contMDiffOn.mono hVU)
    hslots hxV v v
  have h := hlocal v
  rw [hricci, hscale, hslots x hxV, hv] at h
  change mu * (Q * g.inner (f x) w w) ≤ D.ricci (f x) w w at h
  have hfactor : mu / (F.parameters.h t) ^ 2 = mu * Q := by
    dsimp only [Q]
    rw [inv_pow, div_eq_mul_inv]
  change (mu / (F.parameters.h t) ^ 2) * g.inner (f x) w w ≤ D.ricci (f x) w w
  rw [hfactor, mul_assoc]
  exact h

end PoincareConjecture.M47
