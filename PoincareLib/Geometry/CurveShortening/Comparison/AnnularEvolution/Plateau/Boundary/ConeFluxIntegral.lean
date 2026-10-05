import PoincareLib.Geometry.CurveShortening.Comparison.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.ConeFlux

/-!
# Interval flux identities for the general cone

The coordinate-dependent calculation from M65 `InteriorRegularityConeFluxIntegral`
is generalized to a proper real Banach coordinate space. Its generic
AC composition, interpolation and polar transport lemmas are reused
from the independent authorized M65 closure. Source: Morrey ICM 1950,
pp. 183-185; M64 derivation `2026-09-26-general-half-cone.md`.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal InnerProductSpace

namespace PoincareMT.M64BoundaryCone

open M65Interior

variable {C : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- The actual reconstructed angular flux is absolutely continuous. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-general-half-cone.md. -/
theorem coneAngularFlux_AC [CompleteSpace C] [ProperSpace C] {g : C → ℝ}
    {v d : ℝ → C} {v0 : C}
    {r ρ a b s : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (hab : a < b)
    (hv : AbsolutelyContinuousOnInterval v a b)
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ) (hvb : MapsTo v (Icc a b) (closedBall 0 ρ))
    (hd : IntervalIntegrable d volume a b)
    (hinc : ∀ t ∈ Icc a b, ∀ u ∈ Icc a b, v u - v t = ∫ θ in t..u, d θ)
    (hs : s ∈ Icc 0 r) (x : LoopPlane) (test : LoopPlane → ℝ)
    (ht : ContDiff ℝ 1 test) (i : Fin 2) :
    AbsolutelyContinuousOnInterval (fun θ => coneAngularFlux g r v0 v x test i s θ) a b := by
  have hcone := (cone_reconstruction_angular hr hρ hab hv hg h0 hvb hd hinc hs).1
  have hτ : ContDiff ℝ 1 (fun θ => Proofs.M58.angularVector θ i) := by
    fin_cases i
    · exact Real.contDiff_sin.neg
    · exact Real.contDiff_cos
  have hp : ContDiff ℝ 1 (fun θ => polarPlane x (s, θ)) :=
    contDiff_const.add ((Proofs.M58.contDiff_angularPoint.of_le (by simp)).const_smul s)
  exact (hτ.contDiffOn.absolutelyContinuousOnInterval.fun_mul hcone).fun_mul
    (ht.comp hp).contDiffOn.absolutelyContinuousOnInterval

/-- The actual radial derivative integrates to the true outer circle flux. Its zero-radius
term vanishes without a limiting derivative assertion at the center. Proof expansion for
Morgan-Tian (2007), Lemma 19.15, pp. 447-449; M64 derivation
2026-09-26-general-half-cone.md. -/
theorem coneRadialFlux_integral_deriv {g : C → ℝ}
    (v : ℝ → C) {v0 : C}
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ) (θ : ℝ) (hv : v θ ∈ closedBall 0 ρ)
    (x : LoopPlane) (test : LoopPlane → ℝ) (ht : ContDiff ℝ 1 test) (i : Fin 2) :
    (∫ s in (0 : ℝ)..r, deriv (fun q => coneRadialFlux g r v0 v x test i q θ) s) =
      r * Proofs.M58.angularPoint θ i * g (v θ) * test (polarPlane x (r, θ)) := by
  have hc : ContDiff ℝ 1 (fun s => coneCoordinates r v0 v s θ) :=
    contDiff_const.add ((contDiff_id.div_const r).smul contDiff_const)
  have hm : MapsTo (fun s => coneCoordinates r v0 v s θ) (uIcc 0 r) (ball 0 (2 * ρ)) := by
    intro s hs
    rw [uIcc_of_le hr.le] at hs
    exact (closedBall_subset_ball (by linarith)) (coneCoordinates_mem_closedBall hr h0 hv hs)
  have hcone : ContDiffOn ℝ 1 (fun s => g (coneCoordinates r v0 v s θ)) (uIcc 0 r) :=
    hg.comp hc.contDiffOn hm
  have hp : ContDiff ℝ 1 (fun s => polarPlane x (s, θ)) := by
    change ContDiff ℝ 1 (fun s : ℝ => x + s • Proofs.M58.angularPoint θ)
    exact contDiff_const.add (contDiff_id.smul contDiff_const)
  have hflux : ContDiffOn ℝ 1 (fun s => coneRadialFlux g r v0 v x test i s θ) (uIcc 0 r) :=
    ((((contDiff_id : ContDiff ℝ 1 (fun s : ℝ => s)).mul contDiff_const).contDiffOn.mul hcone).mul
      (ht.comp hp).contDiffOn)
  rw [hflux.absolutelyContinuousOnInterval.integral_deriv_eq_sub]
  simp [coneRadialFlux, coneCoordinates, hr.ne']

end PoincareMT.M64BoundaryCone
