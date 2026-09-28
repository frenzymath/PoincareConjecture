import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallFreshCore
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeFreshSlab
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeSharpScalar
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeTerminalScalar
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCenteredNecks
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.CompactBallRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 3200000 in

theorem exists_source_positive_bounded_regular_accuracy
    (P : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon0 → ∀ A1 r B : ℝ, 0 < r → r < A1 → 0 < B →
          ∃ delta : ℝ, 0 < delta ∧ ∀ᶠ k in atTop,
            ∀ (f : UnitTwoSphere → ℝ), Continuous f →
              (∀ q, |f q| < epsilon⁻¹ / 32) →
              ∀ x : H.tubeCriticalRegion T A1 k,
                x.val ∈ (H.tubeMetric T k).ball (H.tubeBase T k) r →
                (H.normalizedSliceConnection k).scalarCurvature x.val.val ≤ B →
                x.val.val ∉ ((T k).list.node 0).2.belowGraph_m28 f →
                x ∈ regularPoints (H.tubeCriticalMetric T A1 k) delta := by
  obtain ⟨epsilonN, hNpos, _, hcentered⟩ :=
    exists_source_tube_centered_strong_necks_accuracy P
  obtain ⟨epsilonS, hSpos, _, hscale⟩ := exists_source_tube_fresh_scale_accuracy.{u}
  obtain ⟨epsilonT, hTpos, _, hterminal⟩ := exists_source_terminal_neck_scalar_accuracy.{u}
  obtain ⟨epsilonR, hRpos, _, hratio⟩ := tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨min (1 / 10000) (min epsilonN (min epsilonS (min epsilonT epsilonR))),
    lt_min (by norm_num) (lt_min hNpos (lt_min hSpos (lt_min hTpos hRpos))),
    min_le_left _ _, ?_⟩
  intro epsilon C A E H T hepsilon A1 r B hr hrA hB
  have hsmall : epsilon ≤ (1 / 10000 : ℝ) := hepsilon.trans (min_le_left _ _)
  have hN : epsilon ≤ epsilonN :=
    hepsilon.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hS : epsilon ≤ epsilonS :=
    hepsilon.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hT : epsilon ≤ epsilonT :=
    hepsilon.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hR : epsilon ≤ epsilonR :=
    hepsilon.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have heps : 0 < epsilon := (T 0).epsilon_eq ▸ (T 0).tube.epsilon_pos
  have hhalf : epsilon < 1 / 2 := hsmall.trans_lt (by norm_num)
  let rmin := (Real.sqrt B)⁻¹
  let delta0 := rmin * epsilon⁻¹ / 200
  let delta := min (delta0 / 4) ((A1 - r) / 4)
  have hrmin : 0 < rmin := inv_pos.mpr (Real.sqrt_pos.mpr hB)
  have hdelta0 : 0 < delta0 := by dsimp [delta0]; positivity
  have hdelta : 0 < delta := lt_min (by positivity) (by positivity)
  have hdeltaSmall : delta ≤ delta0 :=
    (min_le_left _ _).trans (by linarith)
  have hmargin : r + 2 * delta ≤ A1 := by
    have hh : delta ≤ (A1 - r) / 4 := min_le_right _ _
    linarith
  refine ⟨delta, hdelta, ?_⟩
  filter_upwards [hterminal H T hT (2 * B)] with k hk
  intro f hf hbound x hxrad hxscalar hxside
  obtain ⟨J, hJcenter⟩ := hcentered (E (k + H.shift)) (H.segment k)
    (H.base_scalar_pos k) hN (T k) x.val.val x.val.property
  let N := strongNeck_top J hhalf
  have hcenter : N.center = x.val.val := hJcenter
  have hcenterT : N.center ∈ (T k).carrierOpen := by
    rw [hcenter]
    exact x.val.property
  have hcenterB : (H.normalizedSliceConnection k).scalarCurvature N.center ≤ B := by
    rwa [hcenter]
  have hscaleN : N.scale ≤ (101 / 100 : ℝ) * ((T k).list.node 0).2.scale := by
    have hs := hscale H T hS k N hcenterT
    have hzero := H.normalizedSlice_low_neck_scale k ((T k).list.node 0).2
      (T k).node_zero_readout.2.2
    apply (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr (H.base_scalar_pos k))).mp
    nlinarith only [hs, hzero]
  have hexclude : Disjoint N.carrier
      (closure (((T k).list.node (((T k).list.nodes.length - 1 : ℕ) : ℤ)).2.carrier)) := by
    apply Disjoint.closure_right _ N.carrier_open
    apply disjoint_left.mpr
    intro y hyN hyLast
    have hraw := hratio _ _
      ((E (k + H.shift)).flow.connection (E (k + H.shift)).time)
      N hR y hyN N.center (N.central_sphere_subset N.center_on_central_sphere)
    have hnormalized : (H.normalizedSliceConnection k).scalarCurvature y ≤
        2 * (H.normalizedSliceConnection k).scalarCurvature N.center := by
      rw [H.normalizedSlice_scalar_eq, H.normalizedSlice_scalar_eq, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right hraw (H.base_scalar_pos k).le
    have hy := hk y hyLast
    linarith only [hy, hnormalized, hcenterB]
  have hslab := (T k).fresh_three_quarter_slab_subset hsmall f hf hbound N rfl
    hscaleN hcenterT (by rwa [hcenter]) hexclude
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  let s := Real.sqrt Q * N.scale
  have hQ : 0 < Q := H.base_scalar_pos k
  have hs : 0 < s := mul_pos (Real.sqrt_pos.mpr hQ) N.scale_pos
  have hnorm : s ^ 2 * (H.normalizedSliceConnection k).scalarCurvature N.center = 1 := by
    rw [H.normalizedSlice_scalar_eq]
    change s ^ 2 * ((E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, N.center⟩ / Q) = 1
    calc
      _ = N.scale ^ 2 * (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, N.center⟩ := by
        dsimp only [s]
        rw [mul_pow, Real.sq_sqrt hQ.le]
        field_simp
      _ = 1 := tube.neck_normalized_scalar_center N
        ((E (k + H.shift)).flow.connection (E (k + H.shift)).time)
  have hsq : 1 ≤ s ^ 2 * B := by
    rw [← hnorm]
    exact mul_le_mul_of_nonneg_left hcenterB (sq_nonneg s)
  have hprod : 1 ≤ Real.sqrt B * s := by
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
      (mul_nonneg (Real.sqrt_nonneg B) hs.le)).mp
    rw [mul_pow, Real.sq_sqrt hB.le]
    nlinarith only [hsq]
  have hfloor : rmin ≤ Real.sqrt Q * N.scale := by
    change (Real.sqrt B)⁻¹ ≤ s
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hB)).mpr
    nlinarith only [hprod]
  have hzero : (N.coordinate_inverse N.center).2 = 0 :=
    (N.mem_central_sphere_iff_of_mem_carrier
      (N.central_sphere_subset N.center_on_central_sphere)).mp N.center_on_central_sphere
  obtain ⟨hcompact, hclosure⟩ := H.normalizedSlice_fresh_core_compact k N rmin hrmin
    hfloor (N.central_sphere_subset N.center_on_central_sphere)
    (by rw [hzero, abs_zero]; positivity)
  rw [hcenter] at hcompact hclosure
  have hclosureT : closure ((H.normalizedSliceMetric k).ball x.val.val delta0) ⊆
      ((T k).carrierOpen : Set _) := by
    intro y hy
    have hh := hclosure hy
    exact hslab ⟨N.coordinate_inverse y, ⟨mem_univ _, (abs_le.mp hh.2)⟩,
      N.coordinate_map_coordinate_inverse hh.1⟩
  have hcompactTube0 : IsCompact (closure ((H.tubeMetric T k).ball x.val delta0)) :=
    intrinsicOpenMetric_isCompact_closure_ball (H.normalizedSliceMetric k)
      (T k).carrierOpen x.val hcompact hclosureT
  have hcompactTube : IsCompact (closure ((H.tubeMetric T k).ball x.val delta)) := by
    apply hcompactTube0.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro y hy
    exact hy.trans_le (ENNReal.ofReal_le_ofReal hdeltaSmall)
  have hball : (H.tubeMetric T k).ball x.val (2 * delta) ⊆
      (H.tubeCriticalRegion T A1 k : Set (T k).carrierOpen) :=
    riemannian_ball_subset_of_margin (H.tubeMetric T k) hr.le (by positivity) hxrad hmargin
  exact mem_regularPoints_intrinsicOpenMetric_of_compact_ball (H.tubeMetric T k)
    (H.tubeCriticalRegion T A1 k) x hdelta hcompactTube hball

end PoincareConjecture.M28.CounterexampleNeckFamily
