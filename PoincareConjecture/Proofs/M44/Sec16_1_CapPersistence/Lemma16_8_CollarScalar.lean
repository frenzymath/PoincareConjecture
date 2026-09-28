import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_ScalarDoubling
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_ComponentExclusion
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_PinchingBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

theorem regularSlab_not_component_of_collar (P : M44CapPersistencePredecessors.{u})
    (F : SurgeryFlowData.{u}) {a b : ℝ} (S : SurgeryRegularSlab F.slice F.metric a b)
    {U : Set (F.slice a).carrier} (hU : IsPreconnected U)
    {p : (F.slice a).carrier} (hp : p ∈ U) (t : Icc a b) {C : ℝ}
    (v w : TangentSpace (𝓡 3) (S.identify t p))
    (horth : LeviCivitaData.IsOrthonormalPair (F.metric t.1) (S.identify t p) v w)
    (hplane : (F.connection t.1).sectionalCurvature (S.identify t p) v w ≤
      C⁻¹ * (F.connection t.1).scalarCurvature (S.identify t p))
    {x : (F.slice a).carrier} (hx : x ∈ U) :
    ¬ ∃ N : SingularCComponent (F.metric t.1) (F.connection t.1) C,
      S.identify t x ∈ N.carrier :=
  not_component_of_collar_plane
    (hU.image (S.identify t) (S.identify t).continuous.continuousOn)
    (scalar_smooth_of_predecessors P (F.connection t.1)).continuous
    (mem_image_of_mem _ hp) v w horth hplane (mem_image_of_mem _ hx)

theorem exists_collar_scalar_curvature_bound (P : M44CapPersistencePredecessors.{u}) (C : ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ (F : SurgeryFlowData.{u}) {a b : ℝ}
      (S : SurgeryRegularSlab F.slice F.metric a b) {U : Set (F.slice a).carrier},
      IsPreconnected U → ∀ p ∈ U, ∀ {sigma q M : ℝ},
      0 < sigma → sigma ≤ 1 → 0 < M → sigma * q ≤ M →
      (∀ t : Ico a b, ∃ v w : TangentSpace (𝓡 3) (S.identify ⟨t.1, t.2.1, t.2.2.le⟩ p),
        LeviCivitaData.IsOrthonormalPair (F.metric t.1)
          (S.identify ⟨t.1, t.2.1, t.2.2.le⟩ p) v w ∧
        (F.connection t.1).sectionalCurvature
            (S.identify ⟨t.1, t.2.1, t.2.2.le⟩ p) v w ≤
          C⁻¹ * (F.connection t.1).scalarCurvature
            (S.identify ⟨t.1, t.2.1, t.2.2.le⟩ p)) →
      (∀ t : Ico a b, ∀ x ∈ U, q ≤ (S.flow.connection t.1).scalarCurvature x →
        SurgeryCanonicalControl F t.1 (S.identify ⟨t.1, t.2.1, t.2.2.le⟩ x)
          F.parameters.epsilon C) →
      (∀ x ∈ U, sigma * (S.flow.connection a).scalarCurvature x ≤ M) →
      8 * L * M * (b - a) ≤ sigma →
      SurgeryFlowPinched F → Icc a b ⊆ F.time_domain →
      ∀ t : Icc a b, ∀ x ∈ U,
        sigma * (S.flow.connection t.1).scalarCurvature x ≤ 2 * M ∧
        sigma * (F.connection t.1).curvatureTensorNorm (S.identify t x) ≤
          13 * max (2 * M) (Real.exp 4) := by
  obtain ⟨L, hL, hdoubling⟩ := exists_scalar_doubling_constant P C
  refine ⟨L, hL, ?_⟩
  intro F a b S U hU p hp sigma q M hsigma hsmall hM hq hcollar hcanonical
    hinitial htime hpinch hdomain t x hx
  have hthreshold : q ≤ M / sigma :=
    (le_div_iff₀ hsigma).mpr (by simpa only [mul_comm] using hq)
  have htime' : 8 * L * (M / sigma) * (b - a) ≤ 1 := by
    calc
      _ = (8 * L * M * (b - a)) / sigma := by ring
      _ ≤ 1 := (div_le_one hsigma).mpr htime
  have hbound := hdoubling F S U (div_pos hM hsigma) hthreshold
    (fun s y hy hhigh => by
      obtain ⟨v, w, horth, hplane⟩ := hcollar s
      exact ⟨hcanonical s y hy hhigh,
        regularSlab_not_component_of_collar P F S hU hp
          ⟨s.1, s.2.1, s.2.2.le⟩ v w horth hplane hy⟩)
    (fun y hy => (le_div_iff₀ hsigma).mpr (by
      simpa only [mul_comm] using hinitial y hy)) htime' t.1 t.2 x hx
  have hscaled : sigma * (S.flow.connection t.1).scalarCurvature x ≤ 2 * M := by
    calc
      _ ≤ sigma * (2 * (M / sigma)) := mul_le_mul_of_nonneg_left hbound hsigma.le
      _ = 2 * M := by field_simp
  refine ⟨hscaled, ?_⟩
  apply (hpinch t.1 (hdomain t.2)).scaled_curvature_norm_le P (mem_univ _) hsigma.le hsmall
  simpa only [regularSlab_scalar_eq F S t x] using hscaled

end PoincareConjecture.M44
