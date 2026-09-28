import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryLocalizedIntegralVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryCrossEnergy












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Topology ContDiff ENNReal Manifold

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)




theorem localized_source_stress_eq_zero
    (A : M64FreeWeakPhaseAnnulus (n := n) (m := m) e R c0 c1 H0 H1 k D)
    (hc0 : Continuous (e ∘ c0)) (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ x, H0 (x + curvePeriod) = H0 x + D)
    (hH1 : ∀ x, H1 (x + curvePeriod) = H1 x + D)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖Q q‖ ≤ K) (r : ℝ)
    (hmin : ∀ B : M64FreeWeakPhaseAnnulus (n := n) (m := m) e R c0 c1 H0 H1 k D,
      A.annulus.weightedEnergy Q r ≤ B.annulus.weightedEnergy Q r)
    {eta rho : ℝ → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hperiod : Function.Periodic eta curvePeriod) (hzero : eta 0 = 0)
    (hrho : ContDiff ℝ ∞ rho) (hcompact : HasCompactSupport rho) :
    (∫ p in S, deriv eta (p 0) * rho (p 1) *
      (r * Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) -
        r⁻¹ * Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)) +
      r⁻¹ * eta (p 0) * deriv rho (p 1) *
        (Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 1 p) +
          Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 0 p))) = 0 := by
  classical
  obtain ⟨delta, hd, hvar⟩ := m64_exists_localized_horizontal_rectangle_source
    heta hperiod hzero hrho hcompact
  let T : ℝ → LoopPlane ≃ₜ LoopPlane := fun t =>
    if ht : |t| < delta then (hvar t ht).choose else Homeomorph.refl LoopPlane
  have hprops (t : ℝ) (ht : |t| < delta) :
      (∀ x s, T t (annulusPoint x s) = annulusPoint (x + t * eta x * rho s) s) ∧
      ContDiff ℝ ∞ (T t) ∧ ContDiff ℝ ∞ (T t).symm ∧
      (∀ p, ‖fderiv ℝ (T t) p - ContinuousLinearMap.id ℝ LoopPlane‖ ≤ 1 / 2) ∧
      T t ⁻¹' S = S ∧
      (∀ s, StrictMono (fun x => T t (annulusPoint x s) 0)) ∧
      (∀ s, T t (annulusPoint 0 s) = annulusPoint 0 s) ∧
      (∀ s, T t (annulusPoint curvePeriod s) = annulusPoint curvePeriod s) ∧
      ∀ x s, T t (annulusPoint (x + curvePeriod) s) =
        T t (annulusPoint x s) + annulusPoint curvePeriod 0 := by
    simpa only [T, dif_pos ht] using (hvar t ht).choose_spec
  have hsecond (t : ℝ) (p : LoopPlane) : T t p 1 = p 1 := by
    by_cases ht : |t| < delta
    · have hpoint : annulusPoint (p 0) (p 1) = p := by ext i; fin_cases i <;> rfl
      have hp := congrArg (fun q : LoopPlane => q 1) ((hprops t ht).1 (p 0) (p 1))
      rw [hpoint] at hp
      exact hp
    · simp only [T, dif_neg ht, Homeomorph.refl_apply, id_eq]
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, |t| < delta := by
    filter_upwards [ball_mem_nhds (0 : ℝ) hd] with t ht
    simpa only [mem_ball, Real.dist_eq, sub_zero] using ht
  have hactual : ∀ᶠ t : ℝ in 𝓝 0, ∀ x s,
      T t (annulusPoint x s) = annulusPoint (x + t * eta x * rho s) s :=
    hnear.mono fun t ht => (hprops t ht).1
  let f := fun p : LoopPlane =>
    Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p)
  let g := fun p : LoopPlane =>
    Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 1 p) +
      Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 0 p)
  let h := fun p : LoopPlane =>
    Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)
  have ig : Integrable g mu := by
    have h01 : Integrable (fun p =>
        Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 1 p)) mu :=
      A.annulus.column_pair_integrable Q hQ hei hb 0 1
    have h10 : Integrable (fun p =>
        Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 0 p)) mu :=
      A.annulus.column_pair_integrable Q hQ hei hb 1 0
    convert! h01.add h10 using 1
  let J := fun (t : ℝ) (p : LoopPlane) =>
    (r * (1 + t * (deriv eta ((T t).symm p 0) * rho (p 1))) * f p +
      r⁻¹ * (1 + t * (deriv eta ((T t).symm p 0) * rho (p 1)))⁻¹ *
        ((t * (eta ((T t).symm p 0) * deriv rho (p 1))) ^ 2 * f p +
          (t * (eta ((T t).symm p 0) * deriv rho (p 1))) * g p + h p)) / 2
  have hdiff := m64LocalizedSource_integral_firstVariation T hsecond heta hperiod hrho
    hcompact hactual (A.annulus.column_energy_integrable Q hQ hei hb 0) ig
      (A.annulus.column_energy_integrable Q hQ hei hb 1) r
  have hcenter : (∫ p in S, J 0 p) = A.annulus.weightedEnergy Q r := by
    simp only [J, zero_mul, add_zero, inv_one, mul_one, zero_pow (by norm_num : 2 ≠ 0),
      zero_add, M64ObservedWeakAnnulus.weightedEnergy, f, h]
  have hlocal : IsLocalMin (fun t => ∫ p in S, J t p) 0 := by
    filter_upwards [hnear] with t ht
    obtain ⟨hformula, hs, hi, hclose, hpre, -, hz, hP, hshift⟩ := hprops t ht
    have hpos := m64Source_horizontal_derivative_pos hclose
    have hda (p : LoopPlane) : fderiv ℝ (T t) ((T t).symm p) e0 0 =
        1 + t * (deriv eta ((T t).symm p 0) * rho (p 1)) := by
      rw [m64LocalizedSource_horizontal_derivative (hs.differentiable (by simp))
        (heta.differentiable (by simp)) hformula,
        m64TriangularSource_inverse_second (T t) (hsecond t)]
      ring
    have hdb (p : LoopPlane) : fderiv ℝ (T t) ((T t).symm p) e1 0 =
        t * (eta ((T t).symm p 0) * deriv rho (p 1)) := by
      rw [m64LocalizedSource_radial_derivative (hs.differentiable (by simp))
        (hrho.differentiable (by simp)) hformula,
        m64TriangularSource_inverse_second (T t) (hsecond t)]
      ring
    rw [hcenter]
    have hminimum := A.triangular_source_energy_minimum hc0 hc1 hH0 hH1 Q r hmin
      (T t) hs hi (hsecond t) hpos hpre hz hP hshift
    convert! hminimum using 1
    apply integral_congr_ae
    filter_upwards [] with p
    rw [hda, hdb]
    dsimp only [J, f, g, h, m64TriangularEnergyDensity]
    ring
  have hz := hlocal.hasDerivAt_eq_zero hdiff
  rw [integral_div] at hz
  have hnum : (∫ p in S, (r * ((deriv eta (p 0) * rho (p 1)) * f p) +
      r⁻¹ * ((eta (p 0) * deriv rho (p 1)) * g p -
        (deriv eta (p 0) * rho (p 1)) * h p))) = 0 := by linarith
  convert! hnum using 1
  apply integral_congr_ae
  filter_upwards [] with p
  dsimp only [f, g, h]
  ring

end PoincareConjecture.M64FreeWeakPhaseAnnulus
