import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.WeakReplacement
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Product

noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Manifold ContDiff

namespace PoincareConjecture.LeviCivitaData

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem integral_gradient_cutoff_mul_eq (D : LeviCivitaData g)
    {η U : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hU : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ U) (hηc : HasCompactSupport η) :
    (∫ x, g.inner x (D.gradient (fun y => η y * U y) x)
      (D.gradient (fun y => η y * U y) x) ∂g.volumeMeasure) =
      (∫ x, U x ^ 2 * g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure) -
        ∫ x, η x ^ 2 * U x * D.laplacian U x ∂g.volumeMeasure := by
  let f : M → ℝ := fun x => (η x * η x) * U x
  have hfs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := (hη.mul hη).mul hU
  have hfc : HasCompactSupport f := hηc.mul_right.mul_right
  have hpoint (x : M) :
      g.inner x (D.gradient (fun y => η y * U y) x)
        (D.gradient (fun y => η y * U y) x) =
      g.inner x (D.gradient f x) (D.gradient U x) +
        U x ^ 2 * g.inner x (D.gradient η x) (D.gradient η x) := by
    have hηd := (hη x).mdifferentiableAt (by simp)
    have hUd := (hU x).mdifferentiableAt (by simp)
    have hdf := D.gradient_mul (hηd.mul hηd) hUd
    change D.gradient f x = (η x * η x) • D.gradient U x +
      U x • D.gradient (fun y => η y * η y) x at hdf
    rw [D.gradient_mul hηd hηd] at hdf
    rw [hdf, D.gradient_mul hηd hUd]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    rw [g.symm x (D.gradient U x) (D.gradient η x)]
    ring
  have hηi : Integrable (fun x => U x ^ 2 *
      g.inner x (D.gradient η x) (D.gradient η x)) g.volumeMeasure :=
    ((hU.pow 2).continuous.mul (D.continuous_inner_gradient hη hη)).integrable_of_hasCompactSupport
      (D.hasCompactSupport_inner_gradient hηc η).mul_left
  simp_rw [hpoint]
  rw [integral_add (D.integrable_inner_gradient hfs hU hfc) hηi]
  have hgreen := D.integral_mul_laplacian hfs hU hfc
  have hf : (∫ x, η x ^ 2 * U x * D.laplacian U x ∂g.volumeMeasure) =
      ∫ x, f x * D.laplacian U x ∂g.volumeMeasure := by simp only [f, pow_two]
  rw [hf, hgreen]
  ring

theorem integral_gradient_cutoff_mul_le (D : LeviCivitaData g)
    {η U : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hU : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ U) (hηc : HasCompactSupport η)
    {κ : ℝ} (hlap : ∀ x ∈ tsupport η, -(κ * U x ^ 2) ≤ U x * D.laplacian U x) :
    (∫ x, g.inner x (D.gradient (fun y => η y * U y) x)
      (D.gradient (fun y => η y * U y) x) ∂g.volumeMeasure) ≤
      κ * (∫ x, η x ^ 2 * U x ^ 2 ∂g.volumeMeasure) +
        ∫ x, U x ^ 2 * g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure := by
  have hmass : Integrable (fun x => η x ^ 2 * U x ^ 2) g.volumeMeasure :=
    ((hη.pow 2).continuous.mul (hU.pow 2).continuous).integrable_of_hasCompactSupport
      (by
        apply HasCompactSupport.of_support_subset_isCompact hηc
        intro x hx
        by_contra hx'
        exact hx (by simp [image_eq_zero_of_notMem_tsupport hx']))
  have hfc : HasCompactSupport (fun x => η x ^ 2 * U x) := by
    simpa only [pow_two] using
      (show HasCompactSupport (fun x => (η x * η x) * U x) from hηc.mul_right.mul_right)
  have hflap : -κ * (∫ x, η x ^ 2 * U x ^ 2 ∂g.volumeMeasure) ≤
      ∫ x, η x ^ 2 * U x * D.laplacian U x ∂g.volumeMeasure := by
    rw [← integral_const_mul]
    apply integral_mono (hmass.const_mul (-κ))
      (D.integrable_mul_laplacian ((hη.pow 2).mul hU) hU hfc)
    intro x
    change -κ * (η x ^ 2 * U x ^ 2) ≤ η x ^ 2 * U x * D.laplacian U x
    by_cases hx : x ∈ tsupport η
    · have h := mul_le_mul_of_nonneg_left (hlap x hx) (sq_nonneg (η x))
      nlinarith
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [D.integral_gradient_cutoff_mul_eq hη hU hηc]
  linarith

theorem caccioppoli_of_laplacian_lower (D : LeviCivitaData g)
    {η U : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hU : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ U) (hηc : HasCompactSupport η)
    {κ : ℝ} (hlap : ∀ x ∈ tsupport η, -(κ * U x ^ 2) ≤ U x * D.laplacian U x) :
    (∫ x, η x ^ 2 * g.inner x (D.gradient U x) (D.gradient U x) ∂g.volumeMeasure) ≤
      2 * κ * (∫ x, η x ^ 2 * U x ^ 2 ∂g.volumeMeasure) +
      4 * ∫ x, U x ^ 2 * g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure := by
  let f : M → ℝ := fun x => (η x * η x) * U x
  have hfs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := (hη.mul hη).mul hU
  have hfc : HasCompactSupport f := hηc.mul_right.mul_right
  have hmass : Integrable (fun x => η x ^ 2 * U x ^ 2) g.volumeMeasure :=
    ((hη.pow 2).continuous.mul (hU.pow 2).continuous).integrable_of_hasCompactSupport
      (by
        apply HasCompactSupport.of_support_subset_isCompact hηc
        intro x hx
        by_contra hx'
        exact hx (by simp [image_eq_zero_of_notMem_tsupport hx']))
  have hflap : -κ * (∫ x, η x ^ 2 * U x ^ 2 ∂g.volumeMeasure) ≤
      ∫ x, f x * D.laplacian U x ∂g.volumeMeasure := by
    rw [← integral_const_mul]
    apply integral_mono (hmass.const_mul (-κ)) (D.integrable_mul_laplacian hfs hU hfc)
    intro x
    by_cases hx : x ∈ tsupport η
    · have h := mul_le_mul_of_nonneg_left (hlap x hx) (sq_nonneg (η x))
      dsimp only [f]
      nlinarith
    · simp [f, image_eq_zero_of_notMem_tsupport hx]
  have hgreen := D.integral_mul_laplacian hfs hU hfc
  have hcross : (∫ x, g.inner x (D.gradient f x) (D.gradient U x) ∂g.volumeMeasure) ≤
      κ * (∫ x, η x ^ 2 * U x ^ 2 ∂g.volumeMeasure) := by
    rw [hgreen] at hflap
    linarith
  have hfi := D.integrable_inner_gradient hfs hU hfc
  have hηi : Integrable (fun x => U x ^ 2 *
      g.inner x (D.gradient η x) (D.gradient η x)) g.volumeMeasure :=
    ((hU.pow 2).continuous.mul (D.continuous_inner_gradient hη hη)).integrable_of_hasCompactSupport
      (D.hasCompactSupport_inner_gradient hηc η).mul_left
  have hpoint (x : M) :
      η x ^ 2 * g.inner x (D.gradient U x) (D.gradient U x) ≤
        2 * g.inner x (D.gradient f x) (D.gradient U x) +
          4 * (U x ^ 2 * g.inner x (D.gradient η x) (D.gradient η x)) := by
    let v := η x • D.gradient U x + (2 * U x) • D.gradient η x
    have hv : 0 ≤ g.inner x v v := by
      by_cases hz : v = 0
      · simp [hz]
      · exact (g.pos x v hz).le
    have hηd := (hη x).mdifferentiableAt (by simp)
    have hUd := (hU x).mdifferentiableAt (by simp)
    dsimp only [v] at hv
    have hdf := D.gradient_mul (hηd.mul hηd) hUd
    change D.gradient f x = (η x * η x) • D.gradient U x +
      U x • D.gradient (fun y => η y * η y) x at hdf
    rw [D.gradient_mul hηd hηd] at hdf
    rw [hdf]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] at hv
    rw [g.symm x (D.gradient U x) (D.gradient η x)] at hv
    nlinarith
  have hnonneg (x : M) : 0 ≤ η x ^ 2 * g.inner x (D.gradient U x) (D.gradient U x) := by
    apply mul_nonneg (sq_nonneg _)
    by_cases hz : D.gradient U x = 0
    · simp [hz]
    · exact (g.pos x _ hz).le
  have hint := integral_mono_of_nonneg (Eventually.of_forall hnonneg)
    ((hfi.const_mul 2).add (hηi.const_mul 4)) (Eventually.of_forall hpoint)
  simp only [Pi.add_apply] at hint
  rw [integral_add (hfi.const_mul 2) (hηi.const_mul 4),
    integral_const_mul, integral_const_mul] at hint
  linarith

theorem harmonic_caccioppoli (D : LeviCivitaData g)
    {η U : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hU : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ U) (hηc : HasCompactSupport η)
    (hharm : ∀ x ∈ tsupport η, D.laplacian U x = 0) :
    (∫ x, η x ^ 2 * g.inner x (D.gradient U x) (D.gradient U x) ∂g.volumeMeasure) ≤
      4 * ∫ x, U x ^ 2 * g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure := by
  simpa only [mul_zero, zero_mul, zero_add] using
    D.caccioppoli_of_laplacian_lower hη hU hηc (κ := 0)
      (fun x hx => by simp [hharm x hx])

end PoincareConjecture.LeviCivitaData
