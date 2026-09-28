import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarGradientLowerBound
import PoincareConjecture.Proofs.M60.Mathlib.SUCompactMetricCoefficients
import Mathlib.Analysis.Calculus.MeanValue













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)





theorem scalarInverseCoverMap_lipschitzOn
    {H : Plane → ℝ} {V : Cover → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : P ≠ 0) (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip) (htarget : e.target = scalarPotentialStrip)
    (he : (e : Cover → Cover) = scalarNormalizedCoverMap H V P)
    (hes : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target) :
    ∃ K : ℝ≥0, LipschitzOnWith K (scalarInverseCoverMap e) e.target := by
  obtain ⟨c, C, hc, -, hbound⟩ := scalar_cover_potential_uniform_differential_bounds
    D hHc hHs hlap hinner houter hdV P e hsource he hes hei
  have hnon (x : Plane) (hx : x ∈ scalarAnnulus) : fderiv ℝ H x ≠ 0 := by
    intro hzero
    have hb := (hbound x hx).1
    rw [hzero, norm_zero] at hb
    exact hc.not_ge hb
  obtain ⟨b, hb, henergy⟩ :=
    annular_harmonic_gradient_energy_lower_bound D hHc hHs hlap hinner houter hnon
  have hBc : Continuous g.euclideanCoefficients := continuous_iff_continuousAt.mpr
    (fun x => (g.contDiffAt_euclideanCoefficients x).continuousAt)
  obtain ⟨a, ha, hmetric⟩ := M60.suCompactMetric_coercive scalarClosedAnnulus_isCompact
    g.euclideanCoefficients hBc.continuousOn (fun x _ v hv => g.pos x v hv)
  let K : ℝ≥0 := ⟨Real.sqrt ((1 + P ^ 2) / (b * a)), Real.sqrt_nonneg _⟩
  have hKsq : (K : ℝ) ^ 2 = (1 + P ^ 2) / (b * a) :=
    Real.sq_sqrt (div_nonneg (by positivity) (mul_pos hb ha).le)
  have hcoeff : (b * a) * (K : ℝ) ^ 2 = 1 + P ^ 2 := by
    rw [hKsq]
    field_simp
  have hFd (y : Cover) (hy : y ∈ e.target) :
      DifferentiableAt ℝ (scalarInverseCoverMap e) y :=
    ((scalarInverseCoverMap_smooth e hei).contDiffAt
      (e.open_target.mem_nhds hy)).differentiableAt (by simp)
  refine ⟨K, ?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le hFd
  · intro y hy
    change ‖fderiv ℝ (scalarInverseCoverMap e) y‖ ≤ (K : ℝ)
    apply ContinuousLinearMap.opNorm_le_bound _ K.coe_nonneg
    intro v
    have hxA : scalarInverseCoverMap e y ∈ scalarAnnulus :=
      scalarCoverMap_mem (hsource ▸ e.map_target hy)
    have hcoerc := hmetric (scalarInverseCoverMap e y)
      (((scalarAnnulusDefining_pos _).mpr hxA).le) (fderiv ℝ (scalarInverseCoverMap e) y v)
    have hE := henergy _ hxA
    have hnonneg : 0 ≤ g.inner (scalarInverseCoverMap e y)
        (fderiv ℝ (scalarInverseCoverMap e) y v)
        (fderiv ℝ (scalarInverseCoverMap e) y v) := by
      by_cases hz : fderiv ℝ (scalarInverseCoverMap e) y v = 0
      · simp [hz]
      · exact (g.pos _ _ hz).le
    have hidentity := scalarInverseCoverMap_metric_identity D hHs hdV hP
      e hsource he hes hei hy v v
    have hleft : (b * a) * ‖fderiv ℝ (scalarInverseCoverMap e) y v‖ ^ 2 ≤
        v.1 ^ 2 + P ^ 2 * v.2 ^ 2 := by
      calc
        _ = b * (a * ‖fderiv ℝ (scalarInverseCoverMap e) y v‖ ^ 2) := by ring
        _ ≤ b * g.inner (scalarInverseCoverMap e y)
            (fderiv ℝ (scalarInverseCoverMap e) y v)
            (fderiv ℝ (scalarInverseCoverMap e) y v) :=
          mul_le_mul_of_nonneg_left hcoerc hb.le
        _ ≤ _ := by
          have h := mul_le_mul_of_nonneg_right hE hnonneg
          rw [hidentity] at h
          nlinarith
    have hv0 : v.1 ^ 2 ≤ ‖v‖ ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        (sq_le_sq₀ (norm_nonneg v.1) (norm_nonneg v)).mpr (norm_fst_le v)
    have hv1 : v.2 ^ 2 ≤ ‖v‖ ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        (sq_le_sq₀ (norm_nonneg v.2) (norm_nonneg v)).mpr (norm_snd_le v)
    have hright : v.1 ^ 2 + P ^ 2 * v.2 ^ 2 ≤ (1 + P ^ 2) * ‖v‖ ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hv1 (sq_nonneg P)
      nlinarith
    have hsquare : ‖fderiv ℝ (scalarInverseCoverMap e) y v‖ ^ 2 ≤
        ((K : ℝ) * ‖v‖) ^ 2 := by
      apply (mul_le_mul_iff_right₀ (mul_pos hb ha)).mp
      calc
        _ ≤ (1 + P ^ 2) * ‖v‖ ^ 2 := hleft.trans hright
        _ = _ := by rw [mul_pow, ← mul_assoc, hcoeff]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg K.coe_nonneg (norm_nonneg v))).mp hsquare
  · rw [htarget]
    exact (convex_Ioo (0 : ℝ) 1).linear_preimage (LinearMap.fst ℝ ℝ ℝ)

end PoincareConjecture.M64Uniformization
