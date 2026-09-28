import PoincareConjecture.Proofs.M03.Existence.DeTurckDomainRegularityNative
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure












set_option autoImplicit false

open MeasureTheory Set Filter Metric
open scoped Topology SchwartzMap LineDeriv InnerProductSpace

namespace PoincareConjecture.M65Boundary

open EuclideanTranslationNative EuclideanMollificationNative DeTurckDomainRegularityNative

local notation "E" => EuclideanSpace ℝ (Fin 2)



theorem norm_mollify_le_of_ae_bound {ε : ℝ} (hε : 0 < ε)
    (u : ScalarL2 2) {B : ℝ} (hbound : ∀ᵐ z ∂volume, ‖u z‖ ≤ B) (x : E) :
    ‖mollify hε u x‖ ≤ B := by
  have hshift := (Lp.memLp u).comp_measurePreserving
    (Measure.measurePreserving_sub_left volume x)
  have hi : Integrable (fun y => mollifier hε y * u (x - y)) volume := by
    convert! (mollifier_memLp hε).integrable_mul hshift using 1
  have hb := (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae hbound
  rw [mollify_integral]
  calc
    _ ≤ ∫ y, ‖mollifier hε y * u (x - y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, mollifier hε y * B := by
      apply integral_mono_ae hi.norm ((mollifier_integrable hε).mul_const B)
      filter_upwards [hb] with y hy
      change ‖mollifier hε y * u (x - y)‖ ≤ mollifier hε y * B
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (mollifier_nonneg hε y)]
      exact mul_le_mul_of_nonneg_left hy (mollifier_nonneg hε y)
    _ = B := by rw [integral_mul_const, mollifier_integral, one_mul]





theorem weak_equation_bounded_test (A : Fin 2 → ScalarL2 2) (f : E → ℝ)
    (hf : Integrable f volume) {U : Set E} (hU : IsOpen U)
    (heq : ∀ φ : 𝓢(E, ℝ), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪A i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f z * φ z))
    (u : ScalarL2 2) (d : Fin 2 → ScalarL2 2)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    (huK : ∀ᵐ z ∂volume, z ∉ K → u z = 0)
    (hweak : ∀ i (φ : 𝓢(E, ℝ)),
      ⟪d i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u z * fderiv ℝ φ z (EuclideanSpace.single i 1)))
    {B : ℝ} (hbound : ∀ᵐ z ∂volume, ‖u z‖ ≤ B) :
    (∑ i : Fin 2, ⟪A i, d i⟫_ℝ) = -(∫ z, f z * u z) := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open hU hKU
  let eps (n : ℕ) : ℝ := r / ((n : ℝ) + 1)
  have heps (n : ℕ) : 0 < eps n := div_pos hr (by positivity)
  have hepsr (n : ℕ) : eps n ≤ r := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have heps0 : Tendsto eps atTop (𝓝 0) := by
    simpa only [eps, mul_one_div, mul_zero] using
      (tendsto_const_nhds (x := r)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let S (n : ℕ) : 𝓢(E, ℝ) := mollifySchwartz (heps n) u hK huK
  have hconv (w : ScalarL2 2) := tendsto_mollifyL2 eps heps heps0 w
  obtain ⟨σ, hσ, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hconv u)).exists_seq_tendsto_ae
  have hactual : ∀ᵐ z ∂volume, Tendsto (fun n => S (σ n) z) atTop (𝓝 (u z)) := by
    filter_upwards [hpoint, ae_all_iff.mpr (fun n => mollifyL2_ae_eq (heps n) u)]
      with z hz heqz
    exact hz.congr (fun n => heqz (σ n))
  have hSbound (n : ℕ) (z : E) : ‖S n z‖ ≤ B :=
    norm_mollify_le_of_ae_bound (heps n) u hbound z
  have hright : Tendsto (fun n => ∫ z, f z * S (σ n) z) atTop
      (𝓝 (∫ z, f z * u z)) := by
    apply tendsto_integral_of_dominated_convergence (fun z => ‖f z‖ * B)
    · intro n
      exact hf.aestronglyMeasurable.mul (S (σ n)).continuous.aestronglyMeasurable
    · exact hf.norm.mul_const B
    · intro n
      exact Eventually.of_forall (fun z => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hSbound (σ n) z) (norm_nonneg _))
    · filter_upwards [hactual] with z hz
      exact tendsto_const_nhds.mul hz
  have hderiv (i : Fin 2) (n : ℕ) :
      (∂_{EuclideanSpace.single i (1 : ℝ)} (S n)).toLp 2 volume =
        mollifyL2 (heps n) (d i) :=
    lineDeriv_mollifySchwartz_toLp (heps n) u (d i) hK huK
      (EuclideanSpace.single i 1) (hweak i)
  have hleft : Tendsto
      (fun n => ∑ i : Fin 2,
        ⟪A i, (∂_{EuclideanSpace.single i (1 : ℝ)} (S (σ n))).toLp 2 volume⟫_ℝ)
      atTop (𝓝 (∑ i : Fin 2, ⟪A i, d i⟫_ℝ)) := by
    apply tendsto_finsetSum
    intro i _
    simp_rw [hderiv]
    exact tendsto_const_nhds.inner ((hconv (d i)).comp hσ.tendsto_atTop)
  apply tendsto_nhds_unique hleft
  apply hright.neg.congr
  intro n
  exact (heq (S (σ n)) (hasCompactSupport_mollify (heps (σ n)) u hK huK)
    ((tsupport_mollify_subset (heps (σ n)) u huK).trans
      ((cthickening_mono (hepsr (σ n)) K).trans hrU))).symm

end PoincareConjecture.M65Boundary
