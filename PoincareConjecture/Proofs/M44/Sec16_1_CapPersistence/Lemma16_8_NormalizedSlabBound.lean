import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CollarTransport
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CollarScalar
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44




def restrictRegularSlabRight {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {a b c : ℝ}
    (S : SurgeryRegularSlab slice metric a b) (hac : a < c) (hcb : c ≤ b) :
    SurgeryRegularSlab slice metric a c where
  ordered := hac
  flow := Poincare.Geometry.RicciFlow.Harnack.restrictFlow S.flow
    (Icc_subset_Icc le_rfl hcb) ordConnected_Icc
    ⟨a, ⟨le_rfl, hac.le⟩, c, ⟨hac.le, le_rfl⟩, hac.ne⟩
  identify t := S.identify ⟨t.1, t.2.1, t.2.2.trans hcb⟩
  initial_identify := S.initial_identify
  metric_pullback t := S.metric_pullback ⟨t.1, t.2.1, t.2.2.trans hcb⟩





theorem exists_normalized_slab_curvature_bound
    (P : M44CapPersistencePredecessors.{u}) (C : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ (F : SurgeryFlowData.{u}) {a T sigma : ℝ},
      0 < T → 0 < sigma → sigma ≤ 1 →
      ∀ (S : SurgeryRegularSlab F.slice F.metric a (a + T * sigma))
        (G : RicciFlow 3 (F.slice a).carrier (Icc 0 T)),
      (∀ s ∈ Icc (0 : ℝ) T, ∀ x u v,
        (S.flow.metric (a + s * sigma)).inner x u v = sigma * (G.metric s).inner x u v) →
      ∀ (U : Set (F.slice a).carrier), IsPreconnected U → ∀ p ∈ U,
      ∀ {q M : ℝ}, 0 < M → sigma * q ≤ M →
      (∀ t : Ico a (a + T * sigma), ∀ x ∈ U,
        q ≤ (S.flow.connection t.1).scalarCurvature x →
        SurgeryCanonicalControl F t.1 (S.identify ⟨t.1, t.2.1, t.2.2.le⟩ x)
          F.parameters.epsilon C) →
      (∀ x ∈ U, (G.connection 0).scalarCurvature x ≤ M) →
      (∀ s ∈ Ico (0 : ℝ) T, ∃ v w : TangentSpace (𝓡 3) p,
        LeviCivitaData.IsOrthonormalPair (G.metric s) p v w ∧
        (G.connection s).sectionalCurvature p v w < C⁻¹ * (G.connection s).scalarCurvature p) →
      8 * L * M * T ≤ 1 → SurgeryFlowPinched F →
      Icc a (a + T * sigma) ⊆ F.time_domain →
      ∀ s ∈ Icc (0 : ℝ) T, ∀ x ∈ U,
        (G.connection s).scalarCurvature x ≤ 2 * M ∧
        (G.connection s).curvatureTensorNorm x ≤ 13 * max (2 * M) (Real.exp 4) := by
  obtain ⟨L, hL, hbound⟩ := exists_collar_scalar_curvature_bound P C
  refine ⟨L, hL, ?_⟩
  intro F a T sigma hT hsigma hsmall S G hmetric U hU p hp q M hM hq
    hcanonical hinitial hcollar hshort hpinch hdomain
  have htime (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      a + s * sigma ∈ Icc a (a + T * sigma) :=
    ⟨le_add_of_nonneg_right (mul_nonneg hs.1 hsigma.le),
      by linarith only [mul_le_mul_of_nonneg_right hs.2 hsigma.le]⟩
  have hhom (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      MetricHomothety (G.metric s) (F.metric (a + s * sigma))
        (S.identify ⟨a + s * sigma, htime s hs⟩) sigma := by
    intro x v w
    exact (S.metric_pullback ⟨a + s * sigma, htime s hs⟩ x v w).trans
      (hmetric s hs x v w)
  have hscalar (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) (x : (F.slice a).carrier) :
      sigma * (S.flow.connection (a + s * sigma)).scalarCurvature x =
        (G.connection s).scalarCurvature x := by
    have h := M13.homothety_scalarCurvature_eq _ _ _ sigma hsigma (hhom s hs)
      (G.connection s) (F.connection (a + s * sigma)) x
    rw [regularSlab_scalar_eq F S ⟨a + s * sigma, htime s hs⟩ x] at h
    rw [h, mul_div_cancel₀ _ hsigma.ne']
  have hcurv (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) (x : (F.slice a).carrier) :
      (G.connection s).curvatureTensorNorm x = sigma *
        (F.connection (a + s * sigma)).curvatureTensorNorm
          (S.identify ⟨a + s * sigma, htime s hs⟩ x) := by
    have h := M13.homothety_curvatureTensorNorm_eq _ _ _ sigma hsigma (hhom s hs)
      (G.connection s) (F.connection (a + s * sigma)) x
    rw [h, mul_div_cancel₀ _ hsigma.ne']
  have hphysicalCollar (t : Ico a (a + T * sigma)) :
      ∃ v w : TangentSpace (𝓡 3) (S.identify ⟨t.1, t.2.1, t.2.2.le⟩ p),
        LeviCivitaData.IsOrthonormalPair (F.metric t.1)
          (S.identify ⟨t.1, t.2.1, t.2.2.le⟩ p) v w ∧
        (F.connection t.1).sectionalCurvature
          (S.identify ⟨t.1, t.2.1, t.2.2.le⟩ p) v w ≤
            C⁻¹ * (F.connection t.1).scalarCurvature
              (S.identify ⟨t.1, t.2.1, t.2.2.le⟩ p) := by
    let s := (t.1 - a) / sigma
    have hs : s ∈ Ico (0 : ℝ) T := by
      refine ⟨div_nonneg (sub_nonneg.mpr t.2.1) hsigma.le, ?_⟩
      exact (div_lt_iff₀ hsigma).mpr (by linarith only [t.2.2])
    have hclock : a + s * sigma = t.1 := by
      dsimp [s]
      rw [div_mul_cancel₀ _ hsigma.ne']
      ring
    obtain ⟨v, w, horth, hmargin⟩ := hcollar s hs
    have hh := exists_collar_plane_of_homothety (G.connection s)
      (F.connection (a + s * sigma)) (S.identify ⟨a + s * sigma, htime s ⟨hs.1, hs.2.le⟩⟩)
      hsigma (hhom s ⟨hs.1, hs.2.le⟩) p C v w horth hmargin
    let collar (z : Icc a (a + T * sigma)) : Prop :=
      ∃ v w : TangentSpace (𝓡 3) (S.identify z p),
        LeviCivitaData.IsOrthonormalPair (F.metric z.1) (S.identify z p) v w ∧
        (F.connection z.1).sectionalCurvature (S.identify z p) v w <
          C⁻¹ * (F.connection z.1).scalarCurvature (S.identify z p)
    change collar ⟨a + s * sigma, htime s ⟨hs.1, hs.2.le⟩⟩ at hh
    have hz : (⟨a + s * sigma, htime s ⟨hs.1, hs.2.le⟩⟩ : Icc a (a + T * sigma)) =
        ⟨t.1, t.2.1, t.2.2.le⟩ := Subtype.ext hclock
    rw [hz] at hh
    obtain ⟨v', w', horth', hmargin'⟩ := hh
    exact ⟨v', w', horth', hmargin'.le⟩
  have hinitial' (x : (F.slice a).carrier) (hx : x ∈ U) :
      sigma * (S.flow.connection a).scalarCurvature x ≤ M := by
    have h := hscalar 0 ⟨le_rfl, hT.le⟩ x
    calc
      _ = sigma * (S.flow.connection (a + 0 * sigma)).scalarCurvature x :=
        congrArg (fun r => sigma * (S.flow.connection r).scalarCurvature x) (by ring)
      _ ≤ M := h.trans_le (hinitial x hx)
  have hshort' : 8 * L * M * ((a + T * sigma) - a) ≤ sigma := by
    calc
      _ = sigma * (8 * L * M * T) := by ring
      _ ≤ sigma * 1 := mul_le_mul_of_nonneg_left hshort hsigma.le
      _ = sigma := mul_one _
  intro s hs x hx
  obtain ⟨hR, hRm⟩ := hbound F S hU p hp hsigma hsmall hM hq hphysicalCollar
    hcanonical hinitial' hshort' hpinch hdomain ⟨a + s * sigma, htime s hs⟩ x hx
  rw [hscalar s hs x] at hR
  rw [hcurv s hs x]
  exact ⟨hR, hRm⟩

end PoincareConjecture.M44
