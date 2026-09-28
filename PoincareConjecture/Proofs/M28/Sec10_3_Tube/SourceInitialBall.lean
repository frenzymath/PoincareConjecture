import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceSliceNormalization
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckPrecompactBalls
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenMetricBalls
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.Regularity












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}



theorem normalizedSlice_low_neck_scale (H : CounterexampleNeckFamily E) (k : ℕ)
    (N : EpsilonNeck ((E (k + H.shift)).flow.metric (E (k + H.shift)).time))
    (hcenter : N.center = (H.segment k).path (H.segment k).lower) :
    Real.sqrt ((E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩) * N.scale =
        (4 * max C 2)⁻¹ := by
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  have hQ : 0 < Q := H.base_scalar_pos k
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  have hscale := tube.neck_normalized_scalar_center N
    ((E (k + H.shift)).flow.connection (E (k + H.shift)).time)
  change N.scale ^ 2 * (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, N.center⟩ = 1 at hscale
  rw [hcenter, (H.segment k).lower_scalar] at hscale
  change N.scale ^ 2 * (16 * (max C 2) ^ 2 * Q) = 1 at hscale
  have hsquare : (Real.sqrt Q * N.scale * (4 * max C 2)) ^ 2 = 1 := by
    calc
      _ = N.scale ^ 2 * (16 * (max C 2) ^ 2 * Q) := by
        simp only [mul_pow, Real.sq_sqrt hQ.le]
        ring
      _ = 1 := hscale
  have hproduct : Real.sqrt Q * N.scale * (4 * max C 2) = 1 := by
    have hpositive : 0 < Real.sqrt Q * N.scale * (4 * max C 2) :=
      mul_pos (mul_pos (Real.sqrt_pos.mpr hQ) N.scale_pos) (by positivity)
    nlinarith
  change Real.sqrt Q * N.scale = (4 * max C 2)⁻¹
  rw [inv_eq_one_div]
  exact (eq_div_iff (by positivity : (4 * max C 2 : ℝ) ≠ 0)).mpr hproduct



theorem normalizedSlice_low_neck_ball (H : CounterexampleNeckFamily E) (k : ℕ)
    (N : EpsilonNeck ((E (k + H.shift)).flow.metric (E (k + H.shift)).time))
    (hepsilon : N.epsilon = epsilon)
    (hcenter : N.center = (H.segment k).path (H.segment k).lower) :
    (H.normalizedSliceMetric k).ball N.center ((4 * max C 2)⁻¹ * epsilon⁻¹ / 8) =
      ((E (k + H.shift)).flow.metric (E (k + H.shift)).time).ball N.center
        (N.scale * N.epsilon⁻¹ / 8) := by
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  have hQ : 0 < Q := H.base_scalar_pos k
  have hradius : Real.sqrt Q * (N.scale * N.epsilon⁻¹ / 8) =
      (4 * max C 2)⁻¹ * epsilon⁻¹ / 8 := by
    calc
      _ = (Real.sqrt Q * N.scale) * epsilon⁻¹ / 8 := by rw [hepsilon]; ring
      _ = _ := by rw [H.normalizedSlice_low_neck_scale k N hcenter]
  have hball := M13.homothety_ball_image
    ((E (k + H.shift)).flow.metric (E (k + H.shift)).time)
    (H.normalizedSliceMetric k) (Diffeomorph.refl (𝓡 3) _ ∞) Q hQ
    (M13.identity_metricHomothety _ Q hQ) N.center (N.scale * N.epsilon⁻¹ / 8)
  rw [hradius] at hball
  simpa using hball.symm



theorem normalizedSlice_low_neck_regular (H : CounterexampleNeckFamily E) (k : ℕ)
    (N : EpsilonNeck ((E (k + H.shift)).flow.metric (E (k + H.shift)).time))
    (hepsilon : N.epsilon = epsilon)
    (hcenter : N.center = (H.segment k).path (H.segment k).lower)
    (V : TopologicalSpace.Opens
      ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier)
    (hNV : N.carrier ⊆ (V : Set _)) :
    (⟨N.center, hNV (N.central_sphere_subset N.center_on_central_sphere)⟩ : V) ∈
      regularPoints (intrinsicOpenMetric (H.normalizedSliceMetric k) V)
        ((4 * max C 2)⁻¹ * epsilon⁻¹ / 8) := by
  let p : V := ⟨N.center, hNV (N.central_sphere_subset N.center_on_central_sphere)⟩
  let r₀ := (4 * max C 2)⁻¹ * epsilon⁻¹ / 8
  have hcompact := N.precompact_ball_of_central_sphere N.center_on_central_sphere
  rw [← H.normalizedSlice_low_neck_ball k N hepsilon hcenter] at hcompact
  have hclosure : closure ((H.normalizedSliceMetric k).ball (p : _) r₀) ⊆
      (V : Set _) := hcompact.2.trans hNV
  have hball : (H.normalizedSliceMetric k).ball (p : _) r₀ ⊆ (V : Set _) :=
    subset_closure.trans hclosure
  have hcompactV : IsCompact
      (closure ((intrinsicOpenMetric (H.normalizedSliceMetric k) V).ball p r₀)) := by
    rw [intrinsicOpenMetric_closure_ball_eq_preimage _ V p hball]
    apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hcompact.1
    intro x hx
    exact ⟨⟨x, hclosure hx⟩, rfl⟩
  intro r hr
  apply hcompactV.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro x hx
  exact hx.trans_le (ENNReal.ofReal_le_ofReal hr.le)

end CounterexampleNeckFamily




theorem exists_source_initial_ball_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)} (H : CounterexampleNeckFamily E),
        epsilon ≤ epsilon₀ →
        let r₀ := (4 * max C 2)⁻¹ * epsilon⁻¹ / 8
        0 < r₀ ∧ ∀ k : ℕ,
          ∃ N : EpsilonNeck ((E (k + H.shift)).flow.metric (E (k + H.shift)).time),
            N ∈ (H.segment k).cover.necks ∧
            N.center = (H.segment k).path (H.segment k).lower ∧
            IsCompact (closure ((H.normalizedSliceMetric k).ball N.center r₀)) ∧
            closure ((H.normalizedSliceMetric k).ball N.center r₀) ⊆ N.carrier ∧
            ∀ x ∈ closure ((H.normalizedSliceMetric k).ball N.center r₀),
              (H.normalizedSliceConnection k).scalarCurvature x ≤ 32 * (max C 2) ^ 2 := by
  obtain ⟨epsilon₀, hpos, hsmall, hratio⟩ :=
    tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H hbound
  dsimp only
  have hepsilon : 0 < epsilon := by
    rw [← (H.segment 0).cover_epsilon]
    exact (H.segment 0).cover.epsilon_pos
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  refine ⟨by positivity, ?_⟩
  intro k
  have hp : (H.segment k).path (H.segment k).lower ∈ (H.segment k).cover.X := by
    rw [(H.segment k).cover_set]
    exact mem_image_of_mem _ (left_mem_Icc.mpr (H.segment k).lower_lt_upper.le)
  obtain ⟨N, hN, hcenter⟩ := (H.segment k).cover.pointwise_center_cover _ hp
  have heps : N.epsilon = epsilon :=
    ((H.segment k).cover.neck_epsilon N hN).trans (H.segment k).cover_epsilon
  have hcompact := N.precompact_ball_of_central_sphere N.center_on_central_sphere
  rw [← H.normalizedSlice_low_neck_ball k N heps hcenter] at hcompact
  refine ⟨N, hN, hcenter, hcompact.1, hcompact.2, ?_⟩
  intro x hx
  have h := hratio ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier
    ((E (k + H.shift)).flow.metric (E (k + H.shift)).time)
    ((E (k + H.shift)).flow.connection (E (k + H.shift)).time) N
    (heps.trans_le hbound) x (hcompact.2 hx) N.center
    (N.central_sphere_subset N.center_on_central_sphere)
  change (E (k + H.shift)).flow.scalar ⟨(E (k + H.shift)).time, x⟩ ≤
    2 * (E (k + H.shift)).flow.scalar ⟨(E (k + H.shift)).time, N.center⟩ at h
  rw [hcenter, (H.segment k).lower_scalar] at h
  rw [H.normalizedSlice_scalar_eq]
  apply (div_le_iff₀ (H.base_scalar_pos k)).mpr
  nlinarith only [h]

end PoincareConjecture.M28
