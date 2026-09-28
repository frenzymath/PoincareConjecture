import PoincareConjecture.Proofs.M35.CapGeometry.RadialUnitFieldBound
import PoincareConjecture.Proofs.M35.CapGeometry.RadialDerivativeBall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.RepairedStandardCapExistenceData

open M35.Uniqueness

theorem normalized_radial_field_almost_parallel_on_balls
    (P : M35StandardCapPredecessors) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      let Q := (E.flow.connection (t k)).scalarCurvature (x k)
      let hQ := E.scalar_pos (ht k) (x k)
      let G : RiemannianMetric 3 StandardCapSpace :=
        M13.scaleSmoothMetric (E.flow.metric (t k)) Q hQ
      let D := M13.scaleLeviCivitaData (E.flow.connection (t k)) Q hQ
      ∀ y ∈ G.ball (x k) R,
        y ≠ 0 ∧ G.inner y (radialUnitField G y) (radialUnitField G y) = 1 ∧
          ∀ w : StandardCapSpace,
            G.inner y (D.connection (radialUnitField G) y w)
              (D.connection (radialUnitField G) y w) ≤ ε ^ 2 * G.inner y w w := by
  let Q (k : ℕ) := (E.flow.connection (t k)).scalarCurvature (x k)
  have hQ (k : ℕ) : 0 < Q k := E.scalar_pos (ht k) (x k)
  let G (k : ℕ) : RiemannianMetric 3 StandardCapSpace :=
    M13.scaleSmoothMetric (E.flow.metric (t k)) (Q k) (hQ k)
  let D (k : ℕ) := M13.scaleLeviCivitaData (E.flow.connection (t k)) (Q k) (hQ k)
  have heq (k : ℕ) : ((G k).edist 0 (x k)).toReal =
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
  have hgap : 0 < ((G k).edist 0 (x k)).toReal - R := sub_pos.mpr hfar
  have hsmall : 1 / (((G k).edist 0 (x k)).toReal - R) ≤ ε := by
    apply (div_le_iff₀ hgap).mpr
    have h := (div_lt_iff₀ hε).mp
      (show 1 / ε < ((G k).edist 0 (x k)).toReal - R by linarith)
    nlinarith only [h]
  have hrotation := scaleSmoothMetric_rotation_invariant
    (E.rotation_invariant (t k) (ht k)) (Q k) (hQ k)
  have hsec := scaleLeviCivitaData_nonnegative_sectional (E.flow.connection (t k))
    (E.nonnegative_sectional (t k) (ht k)) (Q k) (hQ k)
  have hcomplete := scaleSmoothMetric_complete (E.flow.metric (t k))
    (E.complete (t k) (ht k)) (Q k) (hQ k)
  change ∀ y ∈ (G k).ball (x k) R,
    y ≠ 0 ∧ (G k).inner y (radialUnitField (G k) y) (radialUnitField (G k) y) = 1 ∧
      ∀ w : StandardCapSpace,
        (G k).inner y ((D k).connection (radialUnitField (G k)) y w)
          ((D k).connection (radialUnitField (G k)) y w) ≤ ε ^ 2 * (G k).inner y w w
  intro y hy
  have hyne := (radial_shape_bound_on_ball (D k) hrotation P hsec hcomplete
    (x k) R hfar hy).1
  refine ⟨hyne, radialUnitField_unit (G k) hrotation hyne, ?_⟩
  intro w
  have hww : 0 ≤ (G k).inner y w w := by
    by_cases hw : w = 0
    · simp only [hw, map_zero, le_refl]
    · exact ((G k).pos y w hw).le
  exact (radialUnitField_connection_sq_le_on_ball (D k) hrotation P hsec hcomplete
    (x k) R hfar hy w).trans (mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (one_div_pos.mpr hgap).le hε.le).mpr hsmall) hww)

end PoincareConjecture.RepairedStandardCapExistenceData
