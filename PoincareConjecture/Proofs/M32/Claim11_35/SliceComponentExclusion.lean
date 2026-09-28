import PoincareConjecture.Proofs.M32.Claim11_35.Components.RoundBounds
import PoincareConjecture.Proofs.M32.Claim11_35.Components.CComponentBounds
import PoincareConjecture.Proofs.M32.Mathlib.CompactOpenCapture
import PoincareConjecture.Proofs.M32.Claim11_34.SliceBallCoverage
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space

theorem exists_blowup_slice_closed_component_exclusion :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
        (G : GeneralizedBlowupConvergence S J) {t : ℝ}, t ∈ J →
        ∀ {P : Type v} [TopologicalSpace P]
          (_Phi : (P × ℝ) ≃ₜ G.limit.carrier.carrier)
          {K : Set G.limit.carrier.carrier}, IsCompact K →
          (∀ x ∈ K, 0 < (G.limit.flow.connection t).scalarCurvature x) →
          ∀ {B : ℝ}, 0 < B →
            ∀ᶠ k in atTop, ∃ htk : t ∈ Icc (-G.exhaustion.time k) 0,
              K ⊆ (blowup_sliceEmbedding G k t htk).source ∧
                ∀ x ∈ K,
                  (∀ C : ℝ, C ≤ B → ∀ N : SingularCComponent
                    ((S.flow (G.subsequence k)).metric
                      ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k)))
                    ((S.flow (G.subsequence k)).connection
                      ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))) C,
                    blowup_sliceEmbedding G k t htk x ∉ N.carrier) ∧
                  (∀ epsilon : ℝ, epsilon ≤ epsilon0 → ∀ N : SingularRoundComponent
                    ((S.flow (G.subsequence k)).metric
                      ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))) epsilon,
                    blowup_sliceEmbedding G k t htk x ∉ N.carrier) := by
  obtain ⟨epsilon0, hepsilon0, hepsilon0_le, hround⟩ :=
    exists_round_component_normalized_bounds.{u}
  refine ⟨epsilon0, hepsilon0, hepsilon0_le, ?_⟩
  intro S J G t ht P _ Phi K hK hpositive B hB
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  have hnoncompact : ¬ IsCompact (univ : Set G.limit.carrier.carrier) := by
    intro hc
    let f : G.limit.carrier.carrier → ℝ := fun x => (Phi.symm x).2
    have hf : Continuous f := continuous_snd.comp Phi.symm.continuous
    have hsurj : Function.Surjective f := by
      intro r
      refine ⟨Phi ((Phi.symm G.limit.base).1, r), ?_⟩
      simp only [f, Phi.symm_apply_apply]
    have hcompact : IsCompact (range f) := by
      simpa only [image_univ] using hc.image hf
    exact noncompact_univ ℝ (hsurj.range_eq ▸ hcompact)
  have hf : ContinuousOn (G.limit.flow.connection t).scalarCurvature K :=
    (G.limit.flow.connection t).continuous_scalarCurvature.continuousOn
  obtain ⟨b, hb, hbound⟩ := hK.exists_forall_le' hf hpositive
  let m := b / 2
  have hm : 0 < m := by dsimp [m]; positivity
  let r := max B 32 * m ^ (-1 / 2 : ℝ)
  have hr : 0 < r := mul_pos (hB.trans_le (le_max_left _ _))
    (Real.rpow_pos_of_pos hm _)
  obtain ⟨Kplus, _, hKK, hcover⟩ := blowup_eventually_slice_inverse_balls G ht hK hr
  filter_upwards [hcover, blowup_eventually_sliceScalar_error G ht hK hm] with k hc hs
  obtain ⟨htk, hsource, hballs⟩ := hc
  obtain ⟨htk', _, hscalar⟩ := hs
  refine ⟨htk, hKK.trans hsource, ?_⟩
  intro x hx
  have hnormalized : m ≤ ((S.flow (G.subsequence k)).connection
      ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))).scalarCurvature
        (blowup_sliceEmbedding G k t htk x) / S.scale (G.subsequence k) := by
    have h := hscalar x hx
    change |((S.flow (G.subsequence k)).connection
      ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))).scalarCurvature
      (blowup_sliceEmbedding G k t htk x) / S.scale (G.subsequence k) -
      (G.limit.flow.connection t).scalarCurvature x| < m at h
    have hb' : b = 2 * m := by dsimp [m]; ring
    linarith [(abs_lt.mp h).1, hbound x hx]
  constructor
  · intro C hCB N hmem
    let : LocallyConnectedSpace ((S.flow (G.subsequence k)).slice
        ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))).carrier :=
      ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
    have hopen : IsOpen N.carrier := by
      rw [N.component_eq]
      exact isOpen_connectedComponent
    apply compact_open_not_subset_partial_target (blowup_sliceEmbedding G k t htk)
      hnoncompact N.compact hopen ⟨_, hmem⟩
    have hcarrier := c_component_normalized_carrier N
      (S.base_scalar_pos (G.subsequence k)) hm hCB hmem hnormalized
    intro y hy
    apply ((hballs x hx).2 y ?_).1
    exact (hcarrier hy).trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left B 32) (Real.rpow_nonneg hm.le _)))
  · intro epsilon hepsilon N hmem
    have hopen : IsOpen N.carrier := N.forward_image ▸ N.forward_openEmbedding.isOpen_range
    apply compact_open_not_subset_partial_target (blowup_sliceEmbedding G k t htk)
      hnoncompact N.compact hopen ⟨_, hmem⟩
    have hcarrier := (hround ((S.flow (G.subsequence k)).connection
      ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))) N hepsilon).2
      (S.base_scalar_pos (G.subsequence k)) hm hmem hnormalized
    intro y hy
    apply ((hballs x hx).2 y ?_).1
    exact (hcarrier hy).trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right B 32) (Real.rpow_nonneg hm.le _)))

end PoincareConjecture.M32
