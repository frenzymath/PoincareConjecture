import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Coefficients
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Order.Compact









noncomputable section

open Set Metric Filter Topology
open scoped ContDiff BigOperators InnerProductSpace

namespace Poincare.Analysis.Elliptic

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

open Poincare.Analysis.Sobolev.Weak (matMulE matMulE_ofLp)
open Poincare.Analysis.Sobolev.NirenbergEuclidean

theorem inner_matMulE_eq_sum (A : Matrix (Fin n) (Fin n) ℝ) (v : E) :
    ⟪v, matMulE A v⟫_ℝ = ∑ i, ∑ j, A i j * v i * v j := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, matMulE_ofLp,
    dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem matrix_energy_smul (A : Matrix (Fin n) (Fin n) ℝ) (v : E) (r : ℝ) :
    ⟪r • v, matMulE A (r • v)⟫_ℝ = r ^ 2 * ⟪v, matMulE A v⟫_ℝ := by
  simp only [inner_matMulE_eq_sum, PiLp.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring



theorem exists_uniform_matrix_lower_bound
    {A : E → Matrix (Fin n) (Fin n) ℝ} {K : Set E} (hK : IsCompact K)
    (hA : ∀ i j, ContinuousOn (fun x => A x i j) K)
    (hpos : ∀ x ∈ K, (A x).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ v : E,
      c * ‖v‖ ^ 2 ≤ ⟪v, matMulE (A x) v⟫_ℝ := by
  have hcompact := hK.prod (isCompact_sphere (0 : E) 1)
  have henergy : ContinuousOn (fun z : E × E => ⟪z.2, matMulE (A z.1) z.2⟫_ℝ)
      (K ×ˢ Metric.sphere 0 1) := by
    simp only [inner_matMulE_eq_sum]
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact (((hA i j).comp continuousOn_fst (fun z hz => hz.1)).mul
      ((PiLp.continuous_apply 2 _ i).comp continuous_snd).continuousOn).mul
      ((PiLp.continuous_apply 2 _ j).comp continuous_snd).continuousOn
  obtain ⟨c, hc, hbound⟩ := hcompact.exists_forall_le' henergy (fun z hz => by
    have hv : z.2.ofLp ≠ 0 := by
      intro hv
      have hz0 : z.2 = 0 := by ext i; exact congr_fun hv i
      have hn : ‖z.2‖ = 1 := by simpa [Metric.mem_sphere] using hz.2
      simp [hz0] at hn
    have hp := (hpos z.1 hz.1).dotProduct_mulVec_pos hv
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, matMulE_ofLp,
      dotProduct_comm] using hp)
  refine ⟨c, hc, fun x hx v => ?_⟩
  by_cases hv : v = 0
  · simp [hv, matMulE]
  have hnorm : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := norm_smul_inv_norm hv
  have h := hbound (x, (‖v‖⁻¹ : ℝ) • v)
    ⟨hx, by simpa [Metric.mem_sphere] using hnorm⟩
  calc
    c * ‖v‖ ^ 2 ≤
        ⟪(‖v‖⁻¹ : ℝ) • v, matMulE (A x) ((‖v‖⁻¹ : ℝ) • v)⟫_ℝ * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h (sq_nonneg ‖v‖)
    _ = ⟪v, matMulE (A x) v⟫_ℝ := by
      rw [matrix_energy_smul]
      field_simp [norm_ne_zero_iff.mpr hv]

theorem contDiff_cutoff_mul {O : Set E} (hO : IsOpen O) {η f : E → ℝ}
    (hη : ContDiff ℝ ∞ η) (hf : ContDiffOn ℝ ∞ f O)
    (hsupp : tsupport η ⊆ O) : ContDiff ℝ ∞ (fun x => η x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport η
  · exact hη.contDiffAt.mul (hf.contDiffAt (hO.mem_nhds (hsupp hx)))
  · apply contDiffAt_const.congr_of_eventuallyEq (f := fun _ : E => (0 : ℝ))
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]

theorem matrix_energy_add (A B : Matrix (Fin n) (Fin n) ℝ) (v : E) :
    ⟪v, matMulE (A + B) v⟫_ℝ = ⟪v, matMulE A v⟫_ℝ + ⟪v, matMulE B v⟫_ℝ := by
  simp [inner_matMulE_eq_sum, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem matrix_energy_smul_left (A : Matrix (Fin n) (Fin n) ℝ) (v : E) (r : ℝ) :
    ⟪v, matMulE (r • A) v⟫_ℝ = r * ⟪v, matMulE A v⟫_ℝ := by
  simp [inner_matMulE_eq_sum, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem matrix_energy_one (v : E) :
    ⟪v, matMulE (1 : Matrix (Fin n) (Fin n) ℝ) v⟫_ℝ = ‖v‖ ^ 2 := by
  simp [matMulE]



theorem exists_global_elliptic_extension [NeZero n]
    {O K : Set E} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (A : E → Matrix (Fin n) (Fin n) ℝ) (c : E → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) O)
    (hpos : ∀ x ∈ O, (A x).PosDef) (hc : ContDiffOn ℝ ∞ c O) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ IsCompact (closure V) ∧ closure V ⊆ O ∧
      ∃ B : SmoothEllipticBilinearForm n univ, EqOn B.a A V ∧ EqOn B.c c V := by
  classical
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hKO
  let V := Metric.thickening δ K
  have hcl : closure V ⊆ Metric.cthickening δ K :=
    Metric.closure_thickening_subset_cthickening δ K
  have hVcompact : IsCompact (closure V) := hK.cthickening.of_isClosed_subset
    isClosed_closure hcl
  obtain ⟨η, hη, hηcompact, hηrange, hηone, hηsupp⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff hVcompact hO (hcl.trans hδO)
  obtain ⟨lam, hlam, hlambound⟩ := exists_uniform_matrix_lower_bound hηcompact
    (fun i j => (hA i j).continuousOn.mono hηsupp) (fun x hx => hpos x (hηsupp hx))
  let a : E → Matrix (Fin n) (Fin n) ℝ := fun x =>
    η x • A x + (1 - η x) • (1 : Matrix (Fin n) (Fin n) ℝ)
  have hasymm : ∀ x i j, a x i j = a x j i := by
    intro x i j
    by_cases hx : x ∈ tsupport η
    · have hs : A x i j = A x j i := by
        simpa using ((hpos x (hηsupp hx)).isHermitian.apply j i)
      simp only [a, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hs]
      congr 2
      simp [Matrix.one_apply, eq_comm]
    · simp [a, image_eq_zero_of_notMem_tsupport hx, Matrix.one_apply, eq_comm]
  have hasmooth : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j) := by
    intro i j
    exact (contDiff_cutoff_mul hO hη (hA i j) hηsupp).add
      ((contDiff_const.sub hη).mul contDiff_const)
  have hcoercive : ∀ x : E, ∀ v : E,
      min lam 1 * ‖v‖ ^ 2 ≤ ⟪v, matMulE (a x) v⟫_ℝ := by
    intro x v
    have hη0 : 0 ≤ η x := (hηrange (mem_range_self x)).1
    have hη1 : η x ≤ 1 := (hηrange (mem_range_self x)).2
    by_cases hx : x ∈ tsupport η
    · have hb := mul_le_mul_of_nonneg_left (hlambound x hx v) hη0
      have hminlam := mul_le_mul_of_nonneg_right (min_le_left lam 1) (sq_nonneg ‖v‖)
      have hmin1 := mul_le_mul_of_nonneg_right (min_le_right lam 1) (sq_nonneg ‖v‖)
      have hleft := mul_le_mul_of_nonneg_left hminlam hη0
      have hright := mul_le_mul_of_nonneg_left hmin1 (sub_nonneg.mpr hη1)
      simp only [a, matrix_energy_add, matrix_energy_smul_left, matrix_energy_one]
      nlinarith
    · simp only [a, image_eq_zero_of_notMem_tsupport hx, zero_smul, sub_zero,
        one_smul, zero_add, matrix_energy_one]
      exact (mul_le_mul_of_nonneg_right (min_le_right lam 1) (sq_nonneg ‖v‖)).trans_eq
        (one_mul _)
  let B : SmoothEllipticBilinearForm n univ :=
    { a := a
      c := fun x => η x * c x
      symm := hasymm
      smooth_a := hasmooth
      smooth_c := contDiff_cutoff_mul hO hη hc hηsupp
      lam := min lam 1
      capLam := min lam 1
      hlam_pos := lt_min hlam zero_lt_one
      hlam_le_capLam := le_rfl
      coercive := fun x _ v => hcoercive x v }
  refine ⟨V, Metric.isOpen_thickening, Metric.self_subset_thickening hδ K,
    hVcompact, hcl.trans hδO, B, ?_, ?_⟩
  · intro x hx
    change a x = A x
    simp [a, hηone x (subset_closure hx)]
  · intro x hx
    change η x * c x = c x
    simp [hηone x (subset_closure hx)]

end Poincare.Analysis.Elliptic
