import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverConjugate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology unitInterval

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem scalarCirclePoint_hasDerivAt (r t : ℝ) :
    HasDerivAt (scalarCirclePoint r)
      (fderiv ℝ scalarCoverMap (r, t) (0, 1)) t := by
  have h := (scalarCoverMap_smooth.differentiable (by simp) (r, t)).hasFDerivAt.comp_hasDerivAt
    t ((hasDerivAt_const t r).prodMk (hasDerivAt_id t))
  simpa only [Function.comp_def, scalarCoverMap] using h

theorem scalarFluxPeriod_eq_cover_integral (H : Plane → ℝ) (r : ℝ) :
    scalarFluxPeriod D H r =
      ∫ t in (0 : ℝ)..1, scalarCoverForm D H (r, t) (0, 1) := by
  have hext : EqOn (scalarCirclePath r).extend (scalarCirclePoint r) I := by
    intro t ht
    rw [Path.extend_apply _ ht]
    rfl
  rw [scalarFluxPeriod, curveIntegral_def]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  rw [curveIntegralFun_def, hext ht,
    derivWithin_congr hext (hext ht),
    (scalarCirclePoint_hasDerivAt r t).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc zero_lt_one t ht)]
  rfl

theorem scalarCoverConjugate_increment_eq_period {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    {V : Cover → ℝ}
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {r : ℝ} (hr : r ∈ Ioo (1 : ℝ) 2) :
    V (r, 1) - V (r, 0) = scalarFluxPeriod D H r := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => V (r, s))
      (scalarCoverForm D H (r, t) (0, 1)) t := by
    have h := (hdV (r, t) hr).comp_hasDerivAt t
      ((hasDerivAt_const t r).prodMk (hasDerivAt_id t))
    simpa only [Function.comp_def] using h
  have hβc := (scalarCoverForm_smooth_closed D hHs hlap).1.continuousOn
  have hc : Continuous (fun t : ℝ => scalarCoverForm D H (r, t) (0, 1)) := by
    have hmap : MapsTo (fun t : ℝ => (r, t)) univ scalarCoverStrip := fun _ _ => hr
    have h := hβc.comp (continuous_const.prodMk continuous_id).continuousOn hmap
    exact (continuousOn_univ.mp h).clm_apply continuous_const
  rw [scalarFluxPeriod_eq_cover_integral]
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable 0 1)).symm

theorem exists_annular_cover_conjugate_with_period {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0) :
    ∃ V : Cover → ℝ,
      ContDiffOn ℝ ∞ V scalarCoverStrip ∧
      (∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z) ∧
      ∀ z ∈ scalarCoverStrip,
        V (z + (0, 1)) = V z + scalarFluxPeriod D H (3 / 2) := by
  obtain ⟨V, P, hVs, hdV, hP⟩ := exists_annular_cover_conjugate D hHs hlap
  have hpoint : ((3 / 2 : ℝ), 0) ∈ scalarCoverStrip := by
    norm_num [scalarCoverStrip]
  have heq : P = scalarFluxPeriod D H (3 / 2) := by
    have h := scalarCoverConjugate_increment_eq_period D hHs hlap hdV
      (r := (3 / 2 : ℝ)) (by norm_num)
    have hp := hP _ hpoint
    norm_num only [Prod.mk_add_mk, add_zero, zero_add] at hp
    linarith
  exact ⟨V, hVs, hdV, fun z hz => heq ▸ hP z hz⟩

end PoincareConjecture.M64Uniformization
