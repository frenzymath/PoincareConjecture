import PoincareConjecture.Proofs.M04.CompactDomainParabolic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Linearity











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem nonnegative_of_proper_barrier
    (g : ℝ → RiemannianMetric n M) (D : (t : ℝ) → LeviCivitaData (g t))
    {T N A C : ℝ} (hT : 0 < T) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (f v c : ℝ → M → ℝ) (rho : M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ))
    (hsmooth : ∀ t ∈ Icc 0 T, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f t))
    (hderiv : ∀ t ∈ Icc 0 T, ∀ x : M,
      HasDerivWithinAt (fun s => f s x) (v t x) (Icc 0 T) t)
    (hinit : ∀ x : M, 0 ≤ f 0 x)
    (hlower : ∀ t ∈ Icc 0 T, ∀ x : M, -N ≤ f t x)
    (hcoeff : ∀ t ∈ Icc 0 T, ∀ x : M, c t x ≤ A)
    (hevol : ∀ t ∈ Ioc 0 T, ∀ x : M,
      (D t).laplacian (f t) x + c t x * f t x ≤ v t x)
    (hrho : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho) (hrho1 : ∀ x : M, 1 ≤ rho x)
    (hcompact : ∀ R : ℝ, IsCompact {x : M | rho x ≤ R})
    (hlap : ∀ t ∈ Icc 0 T, ∀ x : M, (D t).laplacian rho x ≤ C * rho x) :
    ∀ t ∈ Icc 0 T, ∀ x : M, 0 ≤ f t x := by
  intro t ht x
  by_contra hbad
  have hneg : f t x < 0 := lt_of_not_ge hbad
  let L := C + A
  have hL : 0 ≤ L := add_nonneg hC hA
  let eps := -f t x / (2 * Real.exp (L * t) * rho x)
  have heps : 0 < eps := div_pos (neg_pos.mpr hneg)
    (mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) (lt_of_lt_of_le zero_lt_one (hrho1 x)))
  let R := max (rho x + 1) (N / eps + 1)
  let K : Set M := {y | rho y ≤ R}
  have hxK : x ∈ K := by
    exact (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1)).trans (le_max_left _ _)
  have hepsR : N < eps * R := by
    have h := mul_le_mul_of_nonneg_left (le_max_right (rho x + 1) (N / eps + 1)) heps.le
    have hcanc : eps * (N / eps) = N := by field_simp
    dsimp only [R]
    rw [mul_add, hcanc, mul_one] at h
    linarith
  let w := fun s y => f s y + eps * Real.exp (L * s) * rho y
  let velocity := fun s y => v s y + eps * Real.exp (L * s) * L * rho y
  have hw : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ K) := by
    apply (hf.mono (prod_mono (Subset.refl _) (subset_univ K))).add
    exact ((continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_fst))).mul
      (hrho.continuous.comp continuous_snd)).continuousOn
  have hdw : ∀ s ∈ Icc 0 T, ∀ y ∈ K,
      HasDerivWithinAt (fun r => w r y) (velocity s y) (Icc 0 T) s := by
    intro s hs y _hy
    have hdexp := ((hasDerivAt_id s).const_mul L).exp
    have hb := ((hdexp.const_mul eps).mul_const (rho y)).hasDerivWithinAt (s := Icc 0 T)
    convert! (hderiv s hs y).add hb using 1
    simp only [id_eq, mul_one]
    ring
  have hwinit (y : M) (_hy : y ∈ K) : 0 ≤ w 0 y := by
    have hterm := mul_nonneg heps.le (le_trans zero_le_one (hrho1 y))
    simpa only [w, mul_zero, Real.exp_zero, mul_one] using add_nonneg (hinit y) hterm
  have hwmin : ∀ s ∈ Ioc 0 T, ∀ y ∈ K,
      (∀ z ∈ K, w s y ≤ w s z) → w s y < 0 → -(-A) * w s y ≤ velocity s y := by
    intro s hs y hy hmin hwneg
    have hsJ : s ∈ Icc 0 T := ⟨hs.1.le, hs.2⟩
    have hexp : 1 ≤ Real.exp (L * s) := Real.one_le_exp (mul_nonneg hL hs.1.le)
    have hrhoy : 0 ≤ rho y := le_trans zero_le_one (hrho1 y)
    have he : 0 ≤ eps * Real.exp (L * s) := mul_nonneg heps.le (Real.exp_nonneg _)
    have hylt : rho y < R := by
      by_contra h
      have hRrho : R ≤ rho y := le_of_not_gt h
      have h1 := mul_le_mul_of_nonneg_left hRrho heps.le
      have h2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp heps.le) hrhoy
      have h3 := hlower s hsJ y
      dsimp only [w] at hwneg
      nlinarith
    have hlocal : IsLocalMin (w s) y := by
      have hopen : IsOpen {z : M | rho z < R} := isOpen_lt hrho.continuous continuous_const
      filter_upwards [hopen.mem_nhds hylt] with z hz
      exact hmin z (le_of_lt hz)
    have hpert : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun z => (eps * Real.exp (L * s)) * rho z) := by
      exact (contDiff_const.mul contDiff_id).contMDiff.comp hrho
    have hwsm : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (w s) := (hsmooth s hsJ).add hpert
    have hlapw := (D s).laplacian_nonneg_of_isLocalMin (hwsm y) hlocal
    have hlapeq : (D s).laplacian (w s) y = (D s).laplacian (f s) y +
        eps * Real.exp (L * s) * (D s).laplacian rho y := by
      rw [show w s = fun z => f s z + (eps * Real.exp (L * s)) * rho z from rfl,
        (D s).laplacian_add (hsmooth s hsJ) hpert,
        (D s).laplacian_const_mul]
    rw [hlapeq] at hlapw
    have hreaction := hevol s hs y
    have hbarrier := mul_le_mul_of_nonneg_left (hlap s hsJ y) he
    have hcoefbar := mul_le_mul_of_nonneg_left (hcoeff s hsJ y) (mul_nonneg he hrhoy)
    have hcoefw := mul_le_mul_of_nonpos_right (hcoeff s hsJ y) hwneg.le
    dsimp only [velocity, w, L] at *
    nlinarith
  have hnonneg := M04.compact_subset_min_velocity_nonnegative (hcompact R)
    (K := -A) hT w velocity hw hdw hwmin hwinit t ht x hxK
  have heq : eps * Real.exp (L * t) * rho x = -f t x / 2 := by
    have hrhone : rho x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (hrho1 x))
    dsimp only [eps]
    field_simp [hrhone]
  dsimp only [w] at hnonneg
  rw [heq] at hnonneg
  linarith

end PoincareConjecture.M34
