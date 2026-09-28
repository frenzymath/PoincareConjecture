import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.SUHopfCoordinates
import PoincareConjecture.Proofs.M60.Mathlib.SUComplexCauchyRiemann
import PoincareConjecture.Proofs.M60.Mathlib.SULiouvilleDecay










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



noncomputable def m60SphereHopfCoefficient (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (z : ℂ) : ℂ :=
  let G := m60AreaGram g (f ∘ m60SphereParameter) (Complex.orthonormalBasisOneI.repr z)
  ((G 0 0 - G 1 1 : ℝ) : ℂ) + Complex.I * ((-2 * G 0 1 : ℝ) : ℂ)



theorem m60SphereHopfCoefficient_differentiable (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hharm : M60SphereChartHarmonic g f) :
    Differentiable ℂ (m60SphereHopfCoefficient g f) := by
  intro z
  have hG (i j : Fin 2) := m60AreaGram_entry_contDiff g
    (hf.comp m60SphereParameter_contMDiff) i j
  have hcr := m60SphereHopf_cauchyRiemann g f hf hharm
    (Complex.orthonormalBasisOneI.repr z)
  apply M60.differentiableAt_complex_of_plane_cauchyRiemann
    (((hG 0 0).sub (hG 1 1)).differentiable (by simp) _)
    ((contDiff_const.mul (hG 0 1)).differentiable (by simp) _)
    hcr.1 hcr.2




theorem m60SphereHopfCoefficient_norm_le (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (z : ℂ) :
    ‖m60SphereHopfCoefficient g f z‖ ≤
      4 * m60SphereEnergyDensity g f (Complex.orthonormalBasisOneI.repr z) := by
  let p := Complex.orthonormalBasisOneI.repr z
  let G := m60AreaGram g (f ∘ m60SphereParameter) p
  have h0 : 0 ≤ G 0 0 := m60AreaGram_diagonal_nonneg g _ p 0
  have h1 : 0 ≤ G 1 1 := m60AreaGram_diagonal_nonneg g _ p 1
  have hdet := m60AreaGram_det_nonneg g (f ∘ m60SphereParameter) p
  rw [Matrix.det_fin_two, m60AreaGram_symm g (f ∘ m60SphereParameter) p 1 0] at hdet
  change 0 ≤ G 0 0 * G 1 1 - G 0 1 * G 0 1 at hdet
  have hreal : |G 0 0 - G 1 1| ≤ G 0 0 + G 1 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have himag : |-2 * G 0 1| ≤ G 0 0 + G 1 1 :=
    abs_le_of_sq_le_sq (by nlinarith [sq_nonneg (G 0 0 - G 1 1)]) (by positivity)
  calc
    ‖m60SphereHopfCoefficient g f z‖ ≤
        ‖((G 0 0 - G 1 1 : ℝ) : ℂ)‖ + ‖Complex.I * ((-2 * G 0 1 : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = |G 0 0 - G 1 1| + |-2 * G 0 1| := by
      rw [norm_mul, Complex.norm_I, one_mul]
      simp only [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 2 * (G 0 0 + G 1 1) := by linarith
    _ = 4 * m60SphereEnergyDensity g f p := by
      unfold m60SphereEnergyDensity m60EnergyDensity
      rw [Matrix.trace_fin_two]
      dsimp only [G]
      ring




theorem m60SphereHopfCoefficient_eq_zero (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hharm : M60SphereChartHarmonic g f) (z : ℂ) : m60SphereHopfCoefficient g f z = 0 := by
  obtain ⟨C, hC, hbound⟩ := m60SphereEnergyDensity_bound g f (hf.of_le (by simp))
  apply M60.complex_eq_zero_of_quartic_decay
    (m60SphereHopfCoefficient_differentiable g f hf hharm) (C := 64 * C) (by positivity) _ z
  intro w
  have h := (m60SphereHopfCoefficient_norm_le g f w).trans
    (mul_le_mul_of_nonneg_left (hbound (Complex.orthonormalBasisOneI.repr w)) (by norm_num))
  calc
    _ ≤ 4 * (C * (16 / (‖Complex.orthonormalBasisOneI.repr w‖ ^ 2 + 4) ^ 2)) := h
    _ = (64 * C) / (‖w‖ ^ 2 + 4) ^ 2 := by
      rw [LinearIsometryEquiv.norm_map]
      ring




theorem m60SphereGram_conformal_of_harmonic (g : RiemannianMetric n M)
    (f : UnitTwoSphere → M) (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f)
    (hharm : M60SphereChartHarmonic g f) (p : LoopPlane) :
    m60AreaGram g (f ∘ m60SphereParameter) p 0 0 =
        m60AreaGram g (f ∘ m60SphereParameter) p 1 1 ∧
      m60AreaGram g (f ∘ m60SphereParameter) p 0 1 = 0 := by
  have h := m60SphereHopfCoefficient_eq_zero g f hf hharm
    (Complex.orthonormalBasisOneI.repr.symm p)
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [m60SphereHopfCoefficient, LinearIsometryEquiv.apply_symm_apply,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, one_mul, zero_add, sub_zero, add_zero,
    Complex.zero_re, Complex.zero_im] at hr hi
  exact ⟨sub_eq_zero.mp hr, by linarith⟩

end PoincareConjecture
