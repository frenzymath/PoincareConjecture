import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ReturnTransverse














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem unequal_boundary_ordered_meeting_velocity_ne
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {alpha beta : ℝ → AnnulusCoordinates} {s t : ℝ}
    (hb : ContDiff ℝ ∞ beta)
    (hga : G.IsGeodesicOn alpha (Icc 0 s)) (hgb : G.IsGeodesicOn beta (Icc 0 t))
    (hs : 0 ≤ s) (hst : s ≤ t)
    (ha0 : ‖alpha 0‖ = 1) (hstart : alpha 0 ≠ beta 0)
    (hbInterior : ∀ x ∈ Ioc 0 t, 1 < ‖beta x‖)
    (hmeet : alpha s = beta t) : deriv alpha s ≠ deriv beta t := by
  intro hvel
  let eta : ℝ → AnnulusCoordinates := fun x => beta (x + (t - s))
  have he : G.IsGeodesicOn eta (Icc 0 s) := by
    intro x hx
    apply hgb.comp_add (t - s)
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hetas : eta s = beta t := by
    dsimp only [eta]
    congr 1
    ring
  have hd : HasDerivAt eta (deriv beta t) s := by
    have h := ((hb.differentiable (by simp) (s + (t - s))).hasDerivAt).scomp s
      ((hasDerivAt_id s).add_const (t - s))
    simpa only [eta, Function.comp_def, id_eq, one_smul,
      show s + (t - s) = t by ring] using! h
  have hcoord : deriv (fun x => extChartAt (𝓡 2) (alpha s) (alpha x)) s =
      deriv (fun x => extChartAt (𝓡 2) (alpha s) (eta x)) s := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
      using hvel.trans hd.deriv.symm
  have heq := hga.eq_nhds_on_of_initial_data he (convex_Icc _ _).isPreconnected
    (t₀ := s) ⟨hs, le_rfl⟩ (alpha s) (by simp)
    (hmeet.trans hetas.symm) hcoord
  have hback : alpha 0 = beta (t - s) := by
    simpa only [eta, zero_add] using
      (heq 0 (show (0 : ℝ) ∈ Icc 0 s from ⟨le_rfl, hs⟩)).self_of_nhds
  rcases hst.eq_or_lt with hst | hst
  · exact hstart (by simpa only [hst, sub_self] using hback)
  · have hnorm := hbInterior (t - s) ⟨sub_pos.mpr hst, by linarith⟩
    rw [← hback, ha0] at hnorm
    exact (lt_irrefl (1 : ℝ)) hnorm





theorem m64Intrinsic_distinct_inward_meeting_velocity_ne
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {alpha beta : ℝ → AnnulusCoordinates} {s t : ℝ}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    (hga : G.IsGeodesicOn alpha (Icc 0 s)) (hgb : G.IsGeodesicOn beta (Icc 0 t))
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (ha0 : ‖alpha 0‖ = 1) (hb0 : ‖beta 0‖ = 1)
    (hstart : alpha 0 ≠ beta 0)
    (haInterior : ∀ x ∈ Ioc 0 s, 1 < ‖alpha x‖)
    (hbInterior : ∀ x ∈ Ioc 0 t, 1 < ‖beta x‖)
    (hmeet : alpha s = beta t) : deriv alpha s ≠ deriv beta t := by
  rcases le_total s t with hst | hts
  · exact unequal_boundary_ordered_meeting_velocity_ne G hb hga hgb hs hst
      ha0 hstart hbInterior hmeet
  · exact Ne.symm (unequal_boundary_ordered_meeting_velocity_ne G ha hgb hga ht hts
      hb0 hstart.symm haInterior hmeet.symm)




theorem m64Intrinsic_inward_meeting_opposite_or_transverse
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {alpha beta : ℝ → AnnulusCoordinates} {s t : ℝ}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    (hga : G.IsGeodesicOn alpha (Icc 0 s)) (hgb : G.IsGeodesicOn beta (Icc 0 t))
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (ha0 : ‖alpha 0‖ = 1) (hb0 : ‖beta 0‖ = 1)
    (hstart : alpha 0 ≠ beta 0)
    (haInterior : ∀ x ∈ Ioc 0 s, 1 < ‖alpha x‖)
    (hbInterior : ∀ x ∈ Ioc 0 t, 1 < ‖beta x‖)
    (haUnit : G.inner (alpha s) (deriv alpha s) (deriv alpha s) = 1)
    (hbUnit : G.inner (beta t) (deriv beta t) (deriv beta t) = 1)
    (hmeet : alpha s = beta t) :
    deriv alpha s = -deriv beta t ∨
      LinearIndependent ℝ (![deriv alpha s, -deriv beta t] : Fin 2 → AnnulusCoordinates) := by
  by_cases hopp : deriv alpha s = -deriv beta t
  · exact Or.inl hopp
  right
  have hsame := m64Intrinsic_distinct_inward_meeting_velocity_ne G ha hb hga hgb hs ht
    ha0 hb0 hstart haInterior hbInterior hmeet
  have hbne : deriv beta t ≠ 0 := by
    intro hz
    simp only [hz, map_zero] at hbUnit
    norm_num at hbUnit
  have hw : G.inner (alpha s) (deriv beta t) (deriv beta t) = 1 := by
    rw [hmeet]
    exact hbUnit
  rw [linearIndependent_fin2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  refine ⟨neg_ne_zero.mpr hbne, ?_⟩
  intro c hc
  have hsq : c ^ 2 = 1 := by
    rw [← hc] at haUnit
    simp only [map_smul, smul_apply, smul_eq_mul, map_neg, neg_apply, hw] at haUnit
    nlinarith only [haUnit]
  have hcCases : c = 1 ∨ c = -1 :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa only [one_pow] using hsq)
  rcases hcCases with rfl | rfl
  · apply hopp
    simpa only [one_smul] using hc.symm
  · apply hsame
    simpa only [neg_one_smul, neg_neg] using hc.symm

end PoincareConjecture
