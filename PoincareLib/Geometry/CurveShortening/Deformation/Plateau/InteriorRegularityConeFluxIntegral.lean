import PoincareLib.Geometry.CurveShortening.Deformation.Compatibility.SourceNames
import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.InteriorRegularityConeFlux

/-!
# Genuine interval flux identities for the cone

The angular flux is actually AC and its matching endpoints give zero
integral derivative. The radial flux is C1 on the genuine closed
radius interval and has the exact outer flux, with its center term
zero. Morrey ICM 1950, printed pp. 183-185, for Morgan--Tian
Lemma 19.2, pp. 437-438; M65 derivation 38, actual cone Green identity.
-/

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace PoincareMT.M65Interior

/-- The actual reconstructed angular flux is absolutely continuous.
Morrey ICM pp. 183-185; MT Lemma 19.2, pp. 437-438; derivation 38. -/
theorem coneAngularFlux_AC {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {v d : ℝ → EuclideanSpace ℝ (Fin 3)} {v0 : EuclideanSpace ℝ (Fin 3)}
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

/-- The genuine angular flux derivative has zero integral by the
actual AC fundamental theorem and the equal circle endpoints.
Morrey ICM pp. 183-185; MT Lemma 19.2, pp. 437-438; derivation 38. -/
theorem coneAngularFlux_integral_deriv {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {v d : ℝ → EuclideanSpace ℝ (Fin 3)} {v0 : EuclideanSpace ℝ (Fin 3)}
    {r ρ s : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hv : AbsolutelyContinuousOnInterval v (-Real.pi) Real.pi)
    (hper : v (-Real.pi) = v Real.pi)
    (hg : ContDiffOn ℝ 1 g (ball 0 (2 * ρ)))
    (h0 : v0 ∈ closedBall 0 ρ)
    (hvb : MapsTo v (Icc (-Real.pi) Real.pi) (closedBall 0 ρ))
    (hd : IntervalIntegrable d volume (-Real.pi) Real.pi)
    (hinc : ∀ t ∈ Icc (-Real.pi) Real.pi, ∀ u ∈ Icc (-Real.pi) Real.pi,
      v u - v t = ∫ θ in t..u, d θ)
    (hs : s ∈ Icc 0 r) (x : LoopPlane) (test : LoopPlane → ℝ)
    (ht : ContDiff ℝ 1 test) (i : Fin 2) :
    (∫ θ in (-Real.pi)..Real.pi,
      deriv (fun q => coneAngularFlux g r v0 v x test i s q) θ) = 0 := by
  rw [(coneAngularFlux_AC hr hρ (by linarith [Real.pi_pos]) hv hg h0 hvb hd hinc
    hs x test ht i).integral_deriv_eq_sub]
  simp [coneAngularFlux, coneCoordinates, hper, polarPlane, Proofs.M58.angularPoint,
    Proofs.M58.angularVector]

/-- The actual radial derivative integrates to the true outer circle
flux. Its zero-radius term vanishes without a limiting derivative
assertion at the center. Morrey ICM pp. 183-185; MT Lemma 19.2,
pp. 437-438; derivation 38. -/
theorem coneRadialFlux_integral_deriv {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (v : ℝ → EuclideanSpace ℝ (Fin 3)) {v0 : EuclideanSpace ℝ (Fin 3)}
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

end PoincareMT.M65Interior
