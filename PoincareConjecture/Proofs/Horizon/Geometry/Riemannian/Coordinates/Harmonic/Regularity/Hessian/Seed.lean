import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.EnergyStep
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.HessianEnergy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.RicciContraction









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology BigOperators ENNReal

namespace PoincareConjecture.HarmonicCoordinates

open LeviCivitaData.Dirichlet

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}


theorem setIntegral_nonneg_lower_of_ellipticity
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S)
    {a b : ℝ} (ha : 0 < a)
    (hell : ∀ x ∈ S, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
        g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2)
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hV : Continuous V)
    (hVn : ∀ x ∈ S, 0 ≤ V x) :
    Real.sqrt (a ^ n) * (∫ x in S, V x) ≤ ∫ x in S, V x ∂g.volumeMeasure := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := OpenPartialHomeomorph.refl E
  have heq : (e : E → E) = id := rfl
  have himage : e '' S = S := by simp only [heq, image_id]
  have hint := integral_compact_image_eq_pullback_density (g := g) e
    contMDiffOn_id contMDiffOn_id hS (by simp [e]) hV.measurable
  rw [himage] at hint
  simp only [heq, id_eq] at hint
  change (∫ x in S, V x ∂g.volumeMeasure) =
    ∫ x in S, V x * g.pullbackVolumeDensity id x at hint
  rw [hint, ← integral_const_mul]
  have hρ : Continuous (g.pullbackVolumeDensity id) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (g.contDiffAt_pullbackVolumeDensity contMDiffAt_id
      (by simpa using Function.injective_id)).1.continuousAt
  apply setIntegral_mono_on
    ((continuous_const.mul hV).continuousOn.integrableOn_compact hS)
    ((hV.mul hρ).continuousOn.integrableOn_compact hS) hS.measurableSet
  intro x hx
  change Real.sqrt (a ^ n) * V x ≤ V x * g.pullbackVolumeDensity id x
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (g.pullbackVolumeDensity_id_bounds x ha (hell x hx)).1 (hVn x hx)

private theorem hessian_seed_metric_nonneg
    (x : EuclideanSpace ℝ (Fin n)) (v : TangentSpace (𝓡 n) x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le



theorem exists_uniform_hessian_energy_seed {a b : ℝ} (ha : 0 < a) (_hb : 0 ≤ b) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 0 < r → ∀ K : ℝ, 0 ≤ K →
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 (2 * r), ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        (∀ x ∈ Metric.ball 0 (2 * r), D.curvatureTensorNorm x ≤ K) →
        ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ f →
        ∀ G : ℝ, 0 ≤ G →
          (∀ x ∈ Metric.ball 0 (2 * r), g.tangentNorm x (D.gradient f x) ≤ G) →
          (∀ x ∈ Metric.ball 0 (2 * r), D.laplacian f =ᶠ[𝓝 x] fun _ => 0) →
          (∫ x in Metric.closedBall 0 (r / 2),
            ∑ i, ∑ j, (D.hessian f x
              (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) ≤
            A * (K + (r ^ 2)⁻¹) * G ^ 2 *
              volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r) := by
  obtain ⟨A0, hA0, hcut⟩ := exists_scaled_energy_cutoff (n := n)
  let A := 4 * Real.sqrt (b ^ n) / Real.sqrt (a ^ n) * ((n : ℝ) + A0 ^ 2 / a)
  refine ⟨A, by dsimp [A]; positivity, fun r hr K hK g D hell hcurv f hf G hG hgrad hharm => ?_⟩
  let S := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r
  let S' := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (r / 2)
  let Q := fun x => ∑ i, ∑ j,
    (D.hessian f x (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2
  let q := fun x => g.inner x (D.gradient f x) (D.gradient f x)
  let V := fun x => Real.sqrt (q x)
  let κ := (n : ℝ) * K
  have hκ : 0 ≤ κ := mul_nonneg (Nat.cast_nonneg n) hK
  have hS : IsCompact S := isCompact_closedBall _ _
  have hS' : IsCompact S' := isCompact_closedBall _ _
  have hSball : S ⊆ Metric.ball 0 (2 * r) := by
    intro x hx
    change dist x 0 < 2 * r
    have hx' : dist x 0 ≤ r := hx
    linarith
  have hinner : S' ⊆ S := Metric.closedBall_subset_closedBall (by linarith)
  obtain ⟨η, hη, hηc, hηS, hηbound, hone, hderiv⟩ := hcut 0 r hr
  have hfs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := contMDiff_iff_contDiff.mpr hf
  have hηs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η := contMDiff_iff_contDiff.mpr hη
  have hq (x) : 0 ≤ q x := hessian_seed_metric_nonneg x _
  have hQ (x) : 0 ≤ Q x :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hqc : Continuous q := (D.contMDiff_inner_gradient hfs hfs).continuous
  have hQc : Continuous Q := (D.contMDiff_hessian_normSq hfs).continuous
  have hVsq (x) : V x ^ 2 = q x := Real.sq_sqrt (hq x)
  have hRic (x) (hx : x ∈ tsupport η) :
      -κ * g.inner x (D.gradient f x) (D.gradient f x) ≤
        D.ricci x (D.gradient f x) (D.gradient f x) := by
    have hbound := D.abs_ricci_le_tangentNorm x (D.gradient f x) (D.gradient f x)
    have hr : |D.ricci x (D.gradient f x) (D.gradient f x)| ≤
        (n : ℝ) * D.curvatureTensorNorm x * q x := by
      change |D.ricci x (D.gradient f x) (D.gradient f x)| ≤
        (n : ℝ) * D.curvatureTensorNorm x * Real.sqrt (q x) * Real.sqrt (q x) at hbound
      calc
        _ ≤ (n : ℝ) * D.curvatureTensorNorm x * Real.sqrt (q x) * Real.sqrt (q x) := hbound
        _ = _ := by rw [mul_assoc, Real.mul_self_sqrt (hq x)]
    have hk : |D.ricci x (D.gradient f x) (D.gradient f x)| ≤ κ * q x :=
      hr.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcurv x (hSball (hηS hx))) (Nat.cast_nonneg n)) (hq x))
    simpa only [neg_mul, q] using (neg_le_neg hk).trans (neg_abs_le _)
  have hbochner := D.harmonic_hessian_energy_le hηs hfs hηc
    (fun x hx => hharm x (hSball (hηS hx))) hRic
  have hweight := weighted_cutoff_energy_le D hS hη (Real.continuous_sqrt.comp hqc)
    hηS (fun x _ => by rw [abs_of_nonneg (hηbound x).1]; exact (hηbound x).2)
    ha (div_nonneg hA0 hr.le) hκ (fun x hx v => (hell x (hSball hx) v).1)
    (fun x _ => hderiv x)
  change κ * (∫ x, η x ^ 2 * V x ^ 2 ∂g.volumeMeasure) +
    (∫ x, V x ^ 2 * g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure) ≤
      (κ + (A0 / r) ^ 2 / a) * ∫ x in S, V x ^ 2 ∂g.volumeMeasure at hweight
  simp_rw [hVsq] at hweight
  have hmass0 : 0 ≤ κ * ∫ x, η x ^ 2 * q x ∂g.volumeMeasure :=
    mul_nonneg hκ (integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hq x))
  have hcutcomm :
      (∫ x, g.inner x (D.gradient η x) (D.gradient η x) * q x ∂g.volumeMeasure) =
      ∫ x, q x * g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure :=
    integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  change (∫ x, η x ^ 2 * Q x ∂g.volumeMeasure) ≤
    2 * κ * (∫ x, η x ^ 2 * q x ∂g.volumeMeasure) +
      4 * ∫ x, g.inner x (D.gradient η x) (D.gradient η x) * q x ∂g.volumeMeasure at hbochner
  rw [hcutcomm] at hbochner
  have henergy : (∫ x, η x ^ 2 * Q x ∂g.volumeMeasure) ≤
      4 * (κ + (A0 / r) ^ 2 / a) * ∫ x in S, q x ∂g.volumeMeasure := by
    nlinarith only [hbochner, hweight, hmass0]
  have hgradSq (x) (hx : x ∈ S) : q x ≤ G ^ 2 := by
    have h := (sq_le_sq₀ (Real.sqrt_nonneg (q x)) hG).mpr (hgrad x (hSball hx))
    rwa [Real.sq_sqrt (hq x)] at h
  have hmass : (∫ x in S, q x ∂g.volumeMeasure) ≤
      Real.sqrt (b ^ n) * G ^ 2 * volume.real S := by
    have hle : (∫ x in S, q x ∂g.volumeMeasure) ≤ ∫ x in S, G ^ 2 ∂g.volumeMeasure :=
      setIntegral_mono_on (hqc.continuousOn.integrableOn_compact hS)
        (continuous_const.continuousOn.integrableOn_compact hS) hS.measurableSet hgradSq
    have hvol := setIntegral_sq_le_of_ellipticity (g := g) hS ha
      (fun x hx => hell x (hSball hx)) (V := fun _ => G) continuous_const
    simp only [setIntegral_const, smul_eq_mul] at hvol
    rw [setIntegral_const, smul_eq_mul] at hle
    calc
      _ ≤ g.volumeMeasure.real S * G ^ 2 := hle
      _ ≤ Real.sqrt (b ^ n) * (volume.real S * G ^ 2) := hvol
      _ = _ := by ring
  have hinnerMass : (∫ x in S', Q x ∂g.volumeMeasure) ≤
      ∫ x, η x ^ 2 * Q x ∂g.volumeMeasure := by
    calc
      _ = ∫ x in S', η x ^ 2 * Q x ∂g.volumeMeasure := by
        apply setIntegral_congr_fun hS'.measurableSet
        intro x hx
        change Q x = η x ^ 2 * Q x
        rw [hone x hx]
        ring
      _ ≤ _ := setIntegral_le_integral (D.integrable_cutoff_hessian_normSq hηs hfs hηc)
        (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (hQ x))
  have hlower := setIntegral_nonneg_lower_of_ellipticity (g := g) hS' ha
    (fun x hx => hell x (hSball (hinner hx))) hQc (fun x _ => hQ x)
  have hden : 0 < Real.sqrt (a ^ n) := Real.sqrt_pos.mpr (pow_pos ha n)
  have hcoef : κ + (A0 / r) ^ 2 / a ≤
      ((n : ℝ) + A0 ^ 2 / a) * (K + (r ^ 2)⁻¹) := by
    have heq : (A0 / r) ^ 2 / a = (A0 ^ 2 / a) * (r ^ 2)⁻¹ := by
      rw [div_pow]
      ring
    rw [heq]
    dsimp only [κ]
    nlinarith only [mul_nonneg (Nat.cast_nonneg n) (inv_nonneg.mpr (sq_nonneg r)),
      mul_nonneg (div_nonneg (sq_nonneg A0) ha.le) hK]
  change (∫ x in S', Q x) ≤ A * (K + (r ^ 2)⁻¹) * G ^ 2 * volume.real S
  apply (mul_le_mul_iff_right₀ hden).mp
  calc
    _ ≤ ∫ x, η x ^ 2 * Q x ∂g.volumeMeasure := hlower.trans hinnerMass
    _ ≤ 4 * (κ + (A0 / r) ^ 2 / a) *
        (Real.sqrt (b ^ n) * G ^ 2 * volume.real S) :=
      henergy.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
    _ ≤ 4 * (((n : ℝ) + A0 ^ 2 / a) * (K + (r ^ 2)⁻¹)) *
        (Real.sqrt (b ^ n) * G ^ 2 * volume.real S) := by gcongr
    _ = _ := by
      dsimp [A]
      field_simp [hden.ne']

end PoincareConjecture.HarmonicCoordinates
