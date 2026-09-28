import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_SpatialPath
import PoincareConjecture.Proofs.M08.ReferenceEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in

theorem seed_curveVelocity_reparameterization {gamma : ℝ → M} {tau d s : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) gamma ((s ^ 2 - tau) / d)) :
    curveVelocity (n := n) (fun z => gamma ((z ^ 2 - tau) / d)) s =
      (2 * s / d) • curveVelocity (n := n) gamma ((s ^ 2 - tau) / d) := by
  have hq : HasDerivAt (fun z : ℝ => (z ^ 2 - tau) / d) (2 * s / d) s := by
    simpa only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] using
      ((hasDerivAt_pow 2 s).sub_const tau).div_const d
  have hqm : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => (z ^ 2 - tau) / d) s 1 =
      (2 * s / d) • (1 : ℝ) := by
    have h := congrArg (fun L : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ]
      TangentSpace 𝓘(ℝ, ℝ) ((s ^ 2 - tau) / d) => L 1)
      hq.hasFDerivAt.hasMFDerivAt.mfderiv
    change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => (z ^ 2 - tau) / d) s (1 : ℝ) =
      (ContinuousLinearMap.toSpanSingleton ℝ (2 * s / d)) (1 : ℝ) at h
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, smul_eq_mul,
      mul_one, one_mul] using h
  have hchain := mfderiv_comp_apply s (f := fun z : ℝ => (z ^ 2 - tau) / d)
    (g := gamma) hgamma hq.differentiableAt.mdifferentiableAt 1
  rw [hqm, map_smul] at hchain
  exact hchain

theorem seed_referenceSpeedSq_bound (g : RiemannianMetric n M)
    {gamma : ℝ → M} (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 gamma)
    {rho tau d s : ℝ} (hrho : 0 ≤ rho)
    (hunit : (s ^ 2 - tau) / d ∈ Icc (0 : ℝ) 1)
    (hspeed : ∀ z ∈ Icc (0 : ℝ) 1, M04.pathSpeed g gamma z ≤ 2 * rho) :
    M08.referenceSpeedSq g (fun z => gamma ((z ^ 2 - tau) / d)) s ≤
      16 * rho ^ 2 * s ^ 2 / d ^ 2 := by
  have hvel := seed_curveVelocity_reparameterization
    ((hgamma _).mdifferentiableAt (by simp)) (tau := tau) (d := d) (s := s)
  have hnonneg := M08.referenceSpeedSq_nonneg g gamma ((s ^ 2 - tau) / d)
  have hnorm : M04.pathSpeed g gamma ((s ^ 2 - tau) / d) ^ 2 =
      M08.referenceSpeedSq g gamma ((s ^ 2 - tau) / d) := Real.sq_sqrt hnonneg
  have hsource : M08.referenceSpeedSq g gamma ((s ^ 2 - tau) / d) ≤ 4 * rho ^ 2 := by
    have h := hspeed _ hunit
    have hp := M04.pathSpeed_nonneg g gamma ((s ^ 2 - tau) / d)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsource (sq_nonneg (2 * s / d))
  dsimp only [M08.referenceSpeedSq] at hmul
  unfold M08.referenceSpeedSq
  simp only [hvel, map_smul, smul_apply, smul_eq_mul]
  change (2 * s / d) * ((2 * s / d) *
      g.inner (gamma ((s ^ 2 - tau) / d))
        (curveVelocity (n := n) gamma ((s ^ 2 - tau) / d))
        (curveVelocity (n := n) gamma ((s ^ 2 - tau) / d))) ≤ _
  calc
    _ = (2 * s / d) ^ 2 * g.inner (gamma ((s ^ 2 - tau) / d))
        (curveVelocity (n := n) gamma ((s ^ 2 - tau) / d))
        (curveVelocity (n := n) gamma ((s ^ 2 - tau) / d)) := by ring
    _ ≤ (2 * s / d) ^ 2 * (4 * rho ^ 2) := hmul
    _ = _ := by ring

end PoincareConjecture.Proofs.M46
