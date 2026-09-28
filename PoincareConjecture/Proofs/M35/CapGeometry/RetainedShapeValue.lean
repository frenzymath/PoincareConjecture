import PoincareConjecture.Proofs.M35.CapGeometry.SelectedBallImage
import PoincareConjecture.Proofs.M35.CapGeometry.FarTipUnitField









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.RepairedStandardCapExistenceData

open M35.Uniqueness



theorem normalized_radial_shape_small_on_balls
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      let Q := (E.flow.connection (t k)).scalarCurvature (x k)
      let G : RiemannianMetric 3 StandardCapSpace :=
        M13.scaleSmoothMetric (E.flow.metric (t k)) Q (E.scalar_pos (ht k) (x k))
      ∀ y ∈ G.ball (x k) R,
        |axisWarpingSlope G ‖y‖ / axisWarpingRadius G ‖y‖| ≤ ε := by
  let Q k := (E.flow.connection (t k)).scalarCurvature (x k)
  have hQ k : 0 < Q k := E.scalar_pos (ht k) (x k)
  let G (k : ℕ) : RiemannianMetric 3 StandardCapSpace :=
    M13.scaleSmoothMetric (E.flow.metric (t k)) (Q k) (hQ k)
  let D (k : ℕ) : LeviCivitaData (G k) :=
    M13.scaleLeviCivitaData (E.flow.connection (t k)) (Q k) (hQ k)
  have heq k : ((G k).edist 0 (x k)).toReal =
      ((E.flow.metric (t k)).edist 0 (x k)).toReal * Real.sqrt (Q k) := by
    have h := M13.homothety_edist (E.flow.metric (t k)) (G k)
      (Diffeomorph.refl (𝓡 3) StandardCapSpace ∞) (Q k) (hQ k)
      (M13.identity_metricHomothety (E.flow.metric (t k)) (Q k) (hQ k)) 0 (x k)
    change (G k).edist 0 (x k) = _ at h
    rw [h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    exact mul_comm _ _
  have hd' : Tendsto (fun k => ((G k).edist 0 (x k)).toReal) atTop atTop := by
    simpa only [heq, Q] using hd
  filter_upwards [hd'.eventually (eventually_gt_atTop (R + 1 / ε))] with k hk
  have hfar : R < ((G k).edist 0 (x k)).toReal :=
    lt_trans (lt_add_of_pos_right R (one_div_pos.mpr hε)) hk
  have hsmall : 1 / (((G k).edist 0 (x k)).toReal - R) ≤ ε := by
    apply (div_le_iff₀ (sub_pos.mpr hfar)).mpr
    have h := (div_lt_iff₀ hε).mp
      (show 1 / ε < ((G k).edist 0 (x k)).toReal - R by linarith)
    nlinarith only [h]
  change ∀ y ∈ (G k).ball (x k) R,
    |axisWarpingSlope (G k) ‖y‖ / axisWarpingRadius (G k) ‖y‖| ≤ ε
  intro y hy
  have hb := radial_shape_bound_on_ball (D k)
    (scaleSmoothMetric_rotation_invariant (E.rotation_invariant (t k) (ht k)) (Q k) (hQ k))
    P (scaleLeviCivitaData_nonnegative_sectional (E.flow.connection (t k))
      (E.nonnegative_sectional (t k) (ht k)) (Q k) (hQ k))
    (scaleSmoothMetric_complete (E.flow.metric (t k))
      (E.complete (t k) (ht k)) (Q k) (hQ k)) (x k) R hfar hy
  rw [abs_of_nonneg hb.2.1]
  exact hb.2.2.trans hsmall

end PoincareConjecture.RepairedStandardCapExistenceData

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness



theorem blowupSequence_far_tip_radial_shape_on_limit_ball
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) (r ε : ℝ) (hε : 0 < ε) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ᶠ k in atTop,
      let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
      let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
      let G := M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
      let phi : L.limit.sliceCarrier.carrier → StandardCapSpace :=
        fun z => ((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
      ∀ z ∈ (L.limit.flow.metric 0).ball L.limit.base r,
        |axisWarpingSlope G ‖phi z‖ / axisWarpingRadius G ‖phi z‖| ≤ ε := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have hsource := E.normalized_radial_shape_small_on_balls P t x ht hd (2 * r) ε hε
  filter_upwards [L.subsequence_strictMono.tendsto_atTop.eventually hsource,
    blowupSequence_image_ball_bounded P E t x ht hR L r] with k hk hball
  dsimp only
  intro z hz
  have hmem := hball ⟨z, hz, rfl⟩
  simp only [blowupSequence_scale] at hmem
  simpa only [blowupSequence_scale] using hk _ hmem

end PoincareConjecture.M35.OrdinaryRealization
