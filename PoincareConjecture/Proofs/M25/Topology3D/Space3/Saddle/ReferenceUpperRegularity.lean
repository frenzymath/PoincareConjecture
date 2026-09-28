import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceBallChart
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

theorem nonnested_reference_positive_height_regular
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d) (hd0 : d 0 = 0)
    (hdNonpos : ∀ q : ℝ, 0 ≤ q → d q ≤ 0)
    (hdDeriv : ∀ q : ℝ, 0 ≤ q → |deriv d q| ≤ 1 / 16)
    (p : UnitTwoSphere) :
    let f : UnitTwoSphere → ℝ := fun q =>
      1 + (q : E3) 2 - ((q : E3) 1) ^ 2 +
        d (((q : E3) 0) ^ 2 + ((q : E3) 1) ^ 2)
    f p ∈ Ioo (0 : ℝ) 2 → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f p ≠ 0 := by
  dsimp only
  intro hp hzero
  let x : ℝ := (p : E3) 0
  let y : ℝ := (p : E3) 1
  let z : ℝ := (p : E3) 2
  let q : ℝ := x ^ 2 + y ^ 2
  let D : ℝ := deriv d q
  let F : E3 → ℝ := fun v => 1 + v 2 - (v 1) ^ 2 + d ((v 0) ^ 2 + (v 1) ^ 2)
  have hc (j : Fin 3) : HasFDerivAt (𝕜 := ℝ) (fun v : E3 => v j)
      (EuclideanSpace.proj (𝕜 := ℝ) j) (p : E3) := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj j : E3 →L[ℝ] ℝ).hasFDerivAt (x := (p : E3))
  have hdq := (hd.differentiable (by simp) q).hasDerivAt.comp_hasFDerivAt
    (p : E3) (((hc 0).pow 2).add ((hc 1).pow 2))
  have hDF := (((hasFDerivAt_const (1 : ℝ) (p : E3)).add (hc 2)).sub
    ((hc 1).pow 2)).add hdq
  change HasFDerivAt F _ (p : E3) at hDF
  have hDF_apply (v : E3) : fderiv ℝ F (p : E3) v =
      v 2 - 2 * y * v 1 + D * (2 * x * v 0 + 2 * y * v 1) := by
    rw [hDF.fderiv]
    simp only [add_apply, sub_apply, smul_apply, smul_eq_mul,
      Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat, zero_add]
    rfl
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let i : UnitTwoSphere → E3 := fun r => (r : E3)
  have hi : MDifferentiableAt (𝓡 2) 𝓘(ℝ, E3) i p :=
    (contMDiff_coe_sphere : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ i).mdifferentiable (by simp) p
  have hchain := hDF.differentiableAt.hasFDerivAt.hasMFDerivAt.comp p hi.hasMFDerivAt
  have hvan (v : E3) (hv : ⟪(p : E3), v⟫_ℝ = 0) : fderiv ℝ F (p : E3) v = 0 := by
    have ht : v ∈ (ℝ ∙ (p : E3))ᗮ :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv
    rw [← range_mvfderiv_subtypeVal (n := 2) p] at ht
    obtain ⟨a, ha⟩ := ht
    change mvfderiv (𝓡 2) i p a = v at ha
    have hzmap : (fderiv ℝ F (p : E3)).comp (mvfderiv (𝓡 2) i p) = 0 :=
      hchain.mfderiv.symm.trans hzero
    have hz := congrArg (fun L : TangentSpace (𝓡 2) p →L[ℝ] ℝ => L a) hzmap
    simpa only [ContinuousLinearMap.comp_apply, zero_apply, ha] using hz
  let v0 : E3 := !₂[z, 0, -x]
  let v1 : E3 := !₂[0, z, -y]
  have hv0 : ⟪(p : E3), v0⟫_ℝ = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Fin.sum_univ_three, star_trivial]
    change z * x + 0 * y + (-x) * z = 0
    ring
  have hv1 : ⟪(p : E3), v1⟫_ℝ = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Fin.sum_univ_three, star_trivial]
    change 0 * x + z * y + (-y) * z = 0
    ring
  have hxD : x * (2 * z * D - 1) = 0 := by
    have hv := hvan v0 hv0
    rw [hDF_apply] at hv
    change -x - 2 * y * 0 + D * (2 * x * z + 2 * y * 0) = 0 at hv
    nlinarith only [hv]
  have hyD : y * (1 + 2 * z * (1 - D)) = 0 := by
    have hv := hvan v1 hv1
    rw [hDF_apply] at hv
    change -y - 2 * y * z + D * (2 * x * 0 + 2 * y * z) = 0 at hv
    nlinarith only [hv]
  have hnorm : ‖(p : E3)‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using p.property
  have hsphere : x ^ 2 + y ^ 2 + z ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) hnorm
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at h
    simpa only [one_pow] using h
  have hq : 0 ≤ q := add_nonneg (sq_nonneg x) (sq_nonneg y)
  have hzabs : |z| ≤ 1 := abs_le.mpr
    ⟨by nlinarith [sq_nonneg x, sq_nonneg y], by nlinarith [sq_nonneg x, sq_nonneg y]⟩
  have hDabs : |D| ≤ 1 / 16 := hdDeriv q hq
  have hmul : |2 * z * D| ≤ 1 / 8 := by
    calc
      |2 * z * D| = 2 * |z| * |D| := by rw [abs_mul, abs_mul]; norm_num
      _ ≤ 2 * 1 * (1 / 16) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hzabs (by norm_num)) hDabs
          (abs_nonneg D) (by norm_num)
      _ = 1 / 8 := by norm_num
  have hx : x = 0 := (mul_eq_zero.mp hxD).resolve_right (by
    have hbound := (abs_le.mp hmul).2
    linarith)
  change 0 < 1 + z - y ^ 2 + d q ∧ 1 + z - y ^ 2 + d q < 2 at hp
  by_cases hy : y = 0
  · have hq0 : q = 0 := by simp [q, hx, hy]
    rw [hq0, hd0, hy] at hp
    rw [hx, hy] at hsphere
    nlinarith [hp.1, hp.2]
  · have heq := (mul_eq_zero.mp hyD).resolve_left hy
    have hDupper := (abs_le.mp hDabs).2
    have hzneg : z < 0 := by
      by_contra hz
      have hz0 : 0 ≤ z := le_of_not_gt hz
      have hproduct : 0 ≤ 2 * z * (1 - D) :=
        mul_nonneg (mul_nonneg (by norm_num) hz0) (by linarith)
      linarith
    have hzprod : z * (z + 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hzneg.le (by linarith [(abs_le.mp hzabs).1])
    have hdnonpos := hdNonpos q hq
    rw [hx] at hsphere
    nlinarith [hp.1]

end PoincareConjecture.M25.Topology3D
