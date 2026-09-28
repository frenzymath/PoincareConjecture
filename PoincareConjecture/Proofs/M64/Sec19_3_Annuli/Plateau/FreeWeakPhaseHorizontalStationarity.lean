import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySourceIntegralVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySourceEnergy

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

theorem horizontal_source_stress_eq_zero
    (A : M64FreeWeakPhaseAnnulus (n := n) (m := m) e R c0 c1 H0 H1 k D)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hei : IsEmbedding e) {K : ℝ} (hb : ∀ q, ‖Q q‖ ≤ K) (r : ℝ)
    (hmin : ∀ B : M64FreeWeakPhaseAnnulus (n := n) (m := m) e R c0 c1 H0 H1 k D,
      A.annulus.weightedEnergy Q r ≤ B.annulus.weightedEnergy Q r)
    {theta : ℝ → ℝ} (htheta : ContDiff ℝ ∞ theta)
    (hperiod : Function.Periodic theta curvePeriod) (hzero : theta 0 = 0) :
    (∫ p in S, deriv theta (p 0) *
      (r * Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p) -
        r⁻¹ * Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p))) = 0 := by
  classical
  obtain ⟨delta, hd, hvar⟩ := M64.smooth_periodic_source_variation htheta hperiod hzero
  let tau : ℝ → ℝ ≃ₜ ℝ := fun t =>
    if ht : |t| < delta then (hvar t ht).choose else Homeomorph.refl ℝ
  have hprops (t : ℝ) (ht : |t| < delta) :
      (∀ x, tau t x = x + t * theta x) ∧ ContDiff ℝ ∞ (tau t) ∧
      ContDiff ℝ ∞ (tau t).symm ∧ StrictMono (tau t) ∧
      (∀ x, 0 < deriv (tau t) x) ∧ tau t 0 = 0 ∧
      ∀ x, tau t (x + curvePeriod) = tau t x + curvePeriod := by
    simpa only [tau, dif_pos ht] using (hvar t ht).choose_spec
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, |t| < delta := by
    filter_upwards [ball_mem_nhds (0 : ℝ) hd] with t ht
    simpa only [mem_ball, Real.dist_eq, sub_zero] using ht
  have hactual : ∀ᶠ t : ℝ in 𝓝 0, ∀ x, tau t x = x + t * theta x :=
    hnear.mono fun t ht => (hprops t ht).1
  let f := fun p : LoopPlane => Q (A.annulus.map p) (A.annulus.column 0 p) (A.annulus.column 0 p)
  let g := fun p : LoopPlane => Q (A.annulus.map p) (A.annulus.column 1 p) (A.annulus.column 1 p)
  let J := fun (t : ℝ) (p : LoopPlane) =>
    (r * (1 + t * deriv theta ((tau t).symm (p 0))) * f p +
      r⁻¹ * (1 + t * deriv theta ((tau t).symm (p 0)))⁻¹ * g p) / 2
  have hdiff := m64HorizontalSource_integral_firstVariation tau htheta hperiod hactual
    (A.annulus.column_energy_integrable Q hQ hei hb 0)
    (A.annulus.column_energy_integrable Q hQ hei hb 1) r
  have hcenter : (∫ p in S, J 0 p) = A.annulus.weightedEnergy Q r := by
    simp only [J, zero_mul, add_zero, inv_one, mul_one, M64ObservedWeakAnnulus.weightedEnergy,
      f, g]
  have hlocal : IsLocalMin (fun t => ∫ p in S, J t p) 0 := by
    filter_upwards [hnear] with t ht
    obtain ⟨hformula, hs, hi, hm, hp, h0, hperiod'⟩ := hprops t ht
    have hderiv (x : ℝ) : deriv (tau t) x = 1 + t * deriv theta x := by
      have heq : (tau t : ℝ → ℝ) = fun x => x + t * theta x := funext hformula
      rw [heq]
      exact ((hasDerivAt_id x).add
        ((htheta.differentiable (by simp) x).hasDerivAt.const_mul t)).deriv
    rw [hcenter]
    simpa only [hderiv, J, f, g] using
      A.horizontal_source_energy_minimum Q r hmin hs hi hp hm h0 hperiod'
  have hz := hlocal.hasDerivAt_eq_zero hdiff
  rw [integral_div] at hz
  linarith

end PoincareConjecture.M64FreeWeakPhaseAnnulus
