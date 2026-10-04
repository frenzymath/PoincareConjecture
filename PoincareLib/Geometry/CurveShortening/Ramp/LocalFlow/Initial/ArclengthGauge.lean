import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Periodic.Arclength
import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.C2.GaugeWitnesses
import PoincareLib.Geometry.CurveShortening.Ramp.Slope.Slope.Regularity

/-!
# Constant-speed normalization of an actual C2 initial curve

The actual metric speed determines a C2 initial label homeomorphism.
The reparameterized curve has constant speed and constant positive
principal coefficient. This is a fixed-time construction for MT2007
Claim 19.1, p. 437 and Lemma 19.6, pp. 441-442; contract review block 8
and `2026-09-21-initial-arclength-gauge.md`, statement 2.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

/-- A periodic C2 immersed curve has an actual C2 degree-one initial
label giving constant speed and constant inverse-squared-speed principal
coefficient. MT2007 Claim 19.1, p. 437 and Lemma 19.6, pp. 441-442;
the initial arclength-gauge derivation, statement 2. -/
theorem exists_c2_constant_speed_relabeling (F : RicciFlow n M (Icc a b))
    (gamma : ℝ → M) (t : ℝ) (hperiod : Function.Periodic gamma curvePeriod)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) :
    let v := curveSpeed F (fun x _ => gamma x) t
    let ell := ∫ x in (0 : ℝ)..curvePeriod, v x
    0 < ell ∧ ∃ phi : ℝ ≃ₜ ℝ,
      (∀ x, phi x = (curvePeriod / ell) * ∫ y in (0 : ℝ)..x, v y) ∧
      ContDiff ℝ 2 (phi : ℝ → ℝ) ∧ ContDiff ℝ 2 (phi.symm : ℝ → ℝ) ∧
      phi 0 = 0 ∧ (∀ x, 0 < deriv phi x) ∧ (∀ y, 0 < deriv phi.symm y) ∧
      (∀ x, phi (x + curvePeriod) = phi x + curvePeriod) ∧
      (∀ y, phi.symm (y + curvePeriod) = phi.symm y + curvePeriod) ∧
      Function.Periodic (fun y => gamma (phi.symm y)) curvePeriod ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => gamma (phi.symm y)) ∧
      (∀ y, curveVelocity (n := n) (fun z => gamma (phi.symm z)) y ≠ 0) ∧
      (∀ y, curveSpeed F (fun z _ => gamma (phi.symm z)) t y = ell / curvePeriod) ∧
      ∀ y, (curveSpeed F (fun z _ => gamma (phi.symm z)) t y ^ 2)⁻¹ =
        (curvePeriod / ell) ^ 2 := by
  let v := curveSpeed F (fun x _ => gamma x) t
  let ell := ∫ x in (0 : ℝ)..curvePeriod, v x
  have hp : 0 < curvePeriod := Real.two_pi_pos
  have hv : ContDiff ℝ 1 v := speed_contDiff_of_c2 F (fun x _ => gamma x) hgamma himm
  have hreg : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) gamma := hgamma.mdifferentiable (by norm_num)
  have hvpos (x : ℝ) : 0 < v x := Real.sqrt_pos.mpr ((F.metric t).pos _ _ (himm x))
  have hvperiod : Function.Periodic v curvePeriod := by
    have hX := m63CurveVelocity_periodic hreg hperiod
    intro x
    have hvel : curveVelocity gamma (x + curvePeriod) = curveVelocity gamma x := hX x
    have hbase : gamma (x + curvePeriod) = gamma x := hperiod x
    change (F.metric t).tangentNorm (gamma (x + curvePeriod))
        (curveVelocity gamma (x + curvePeriod)) =
      (F.metric t).tangentNorm (gamma x) (curveVelocity gamma x)
    erw [hvel, hbase]
  obtain ⟨hell, phi, hformula, hphi, hinv, hzero, hshift, hinvshift, hd, hdinv⟩ :=
    exists_periodic_arclength_homeomorph hp hv hvperiod hvpos
  have hspeed (y : ℝ) :
      curveSpeed F (fun z _ => gamma (phi.symm z)) t y = ell / curvePeriod := by
    have hscale : 0 < ell / (curvePeriod * v (phi.symm y)) :=
      div_pos hell (mul_pos hp (hvpos _))
    calc
      _ = (ell / (curvePeriod * v (phi.symm y))) * v (phi.symm y) :=
        curveSpeed_comp F (fun x _ => gamma x) (hreg _) (hdinv y).1 hscale.le
      _ = ell / curvePeriod := by field_simp [(hvpos (phi.symm y)).ne']
  refine ⟨hell, phi, hformula, hphi, hinv, hzero, fun x => (hd x).2,
    fun y => (hdinv y).2, hshift, hinvshift, ?_, ?_, ?_, hspeed, ?_⟩
  · intro y
    dsimp only
    rw [hinvshift, hperiod]
  · exact hgamma.comp hinv.contMDiff
  · intro y
    rw [curveVelocity_comp (hreg _) (hdinv y).1]
    exact smul_ne_zero (div_pos hell (mul_pos hp (hvpos _))).ne' (himm _)
  · intro y
    rw [hspeed]
    change ((ell / curvePeriod) ^ 2)⁻¹ = (curvePeriod / ell) ^ 2
    rw [← inv_pow, inv_div]

end PoincareMT.M63
