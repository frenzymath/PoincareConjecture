import PoincareConjecture.Proofs.M47.JointSeedSquarePath

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M47

theorem jointSeed_radial_parameter_bounds {d v s : ℝ}
    (hv : 0 < v) (hvd : v < d)
    (hs : s ∈ Icc (Real.sqrt (d - v)) (Real.sqrt (d - v / 2))) :
    0 ≤ s ∧ d - v ≤ s ^ 2 ∧ s ^ 2 ≤ d - v / 2 ∧
      2 * (s ^ 2 - (d - v)) / v ∈ Icc (0 : ℝ) 1 := by
  have hpos : 0 < d - v := sub_pos.mpr hvd
  have htheta : 0 < d - v / 2 := by linarith
  have hspos : 0 ≤ s := (Real.sqrt_nonneg _).trans hs.1
  have hslo : d - v ≤ s ^ 2 := by
    simpa only [Real.sq_sqrt hpos.le] using
      (sq_le_sq₀ (Real.sqrt_nonneg (d - v)) hspos).2 hs.1
  have hshi : s ^ 2 ≤ d - v / 2 := by
    simpa only [Real.sq_sqrt htheta.le] using
      (sq_le_sq₀ hspos (Real.sqrt_nonneg (d - v / 2))).2 hs.2
  refine ⟨hspos, hslo, hshi, div_nonneg (by linarith) hv.le, ?_⟩
  apply (div_le_one hv).2
  linarith

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem jointSeed_radial_square_curve_smooth (gamma : ℝ → M)
    (hgamma : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ gamma) (d v : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (fun s => gamma (2 * (s ^ 2 - (d - v)) / v)) :=
  hgamma.comp
    (((contDiff_const.mul ((contDiff_id.pow 2).sub contDiff_const)).div_const v).contMDiff)

set_option backward.isDefEq.respectTransparency false in

theorem jointSeed_radial_square_velocity (gamma : ℝ → M)
    (hgamma : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ gamma) (d v s : ℝ) :
    curveVelocity (n := n) (fun z => gamma (2 * (z ^ 2 - (d - v)) / v)) s =
      (4 * s / v) • curveVelocity (n := n) gamma (2 * (s ^ 2 - (d - v)) / v) := by
  let phi (z : ℝ) := 2 * (z ^ 2 - (d - v)) / v
  have hphi : HasDerivAt phi (4 * s / v) s := by
    convert! ((((hasDerivAt_id s).pow 2).sub_const (d - v)).const_mul 2).div_const v using 1
    dsimp only [id]
    ring
  have hinput : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) phi s 1 = 4 * s / v := by
    rw [mfderiv_eq_fderiv]
    exact hphi.deriv
  have hchain := mfderiv_comp_apply s (f := phi) (g := gamma)
    ((hgamma (phi s)).mdifferentiableAt (by simp))
    hphi.differentiableAt.mdifferentiableAt (1 : TangentSpace (𝓘(ℝ, ℝ)) s)
  rw [hinput, show 4 * s / v = (4 * s / v) • (1 : ℝ) by simp, map_smul] at hchain
  exact hchain

variable [IsManifold (𝓡 n) ∞ M]

theorem jointSeed_radial_square_reference_energy
    (g : RiemannianMetric n M) (gamma : ℝ → M)
    (hgamma : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ gamma) {d v s r : ℝ} (hr : 0 ≤ r)
    (hspeed : g.tangentNorm (gamma (2 * (s ^ 2 - (d - v)) / v))
      (curveVelocity (n := n) gamma (2 * (s ^ 2 - (d - v)) / v)) ≤ r) :
    g.inner (gamma (2 * (s ^ 2 - (d - v)) / v))
      (curveVelocity (n := n) (fun z => gamma (2 * (z ^ 2 - (d - v)) / v)) s)
      (curveVelocity (n := n) (fun z => gamma (2 * (z ^ 2 - (d - v)) / v)) s) ≤
        (4 * s / v) ^ 2 * r ^ 2 := by
  let x := gamma (2 * (s ^ 2 - (d - v)) / v)
  let w := curveVelocity (n := n) gamma (2 * (s ^ 2 - (d - v)) / v)
  have hnonneg : 0 ≤ g.inner x w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact (g.pos x w hw).le
  have hsquare : g.inner x w w ≤ r ^ 2 := by
    have h := (sq_le_sq₀ (Real.sqrt_nonneg _) hr).2 hspeed
    change (Real.sqrt (g.inner x w w)) ^ 2 ≤ r ^ 2 at h
    rwa [Real.sq_sqrt hnonneg] at h
  rw [jointSeed_radial_square_velocity gamma hgamma d v s]
  simp only [map_smul, smul_apply, smul_eq_mul]
  have h := mul_le_mul_of_nonneg_left hsquare (sq_nonneg (4 * s / v))
  dsimp only [x, w] at h
  nlinarith

end PoincareConjecture.M47
