import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryMixedTests












set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

set_option maxHeartbeats 800000 in





theorem m64NaturalGrowth_mixed_potential_bound
    {n : ℕ} (dirichlet : Fin n → Prop) {O : Set LoopPlane} (hO : IsOpen O)
    {F du : Fin n → Fin 2 → LoopPlane → ℝ} {b u : Fin n → LoopPlane → ℝ}
    {xi H W : LoopPlane → ℝ} {nu B delta C0 : ℝ}
    (hnu : 0 < nu) (hsmall : B * delta ≤ nu / 4)
    (hH : ∀ p, 0 ≤ H p) (hW : ∀ p, 0 ≤ W p)
    (hF : ∀ k i, MemLp (F k i) 2 volume) (hb : ∀ k, Integrable (b k))
    (hu : ∀ k, Continuous (u k)) (hdu : ∀ k i, MemLp (du k i) 2 volume)
    (hw : ∀ k i, HasWeakPartialDeriv i (du k i) (u k) univ)
    (hz : ∀ k, dirichlet k → ∀ p : LoopPlane, p 1 < 0 → u k p = 0)
    (hxi : ContDiff ℝ ∞ xi) (hc : HasCompactSupport xi) (hs : tsupport xi ⊆ O)
    (heq : ∀ k (phi : LoopPlane → ℝ), ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O → (dirichlet k → ∀ p : LoopPlane, p 1 = 0 → phi p = 0) →
      (∫ p, ∑ i : Fin 2, F k i p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p, b k p * phi p)
    (hcoercive : ∀ p, nu * H p - C0 ≤ ∑ k, ∑ i, F k i p * du k i p)
    (hsource : ∀ p, (∑ k, b k p * u k p) ≤ B * delta * H p)
    (hcross : ∀ p, (∑ k, ∑ i, F k i p * u k p *
      fderiv ℝ xi p (EuclideanSpace.single i 1)) ^ 2 ≤
      B ^ 2 * delta ^ 2 * H p * W p *
        ∑ i : Fin 2, (fderiv ℝ xi p (EuclideanSpace.single i 1)) ^ 2)
    (hHI : Integrable (fun p => H p * xi p ^ 2))
    (hWI : Integrable (fun p => W p *
      ∑ i : Fin 2, (fderiv ℝ xi p (EuclideanSpace.single i 1)) ^ 2)) :
    nu / 2 * (∫ p, H p * xi p ^ 2) ≤ C0 * (∫ p, xi p ^ 2) +
      (4 * B ^ 2 * delta ^ 2 / nu) *
        ∫ p, W p * ∑ i : Fin 2, (fderiv ℝ xi p (EuclideanSpace.single i 1)) ^ 2 := by
  let dxi (i : Fin 2) (p : LoopPlane) := fderiv ℝ xi p (EuclideanSpace.single i 1)
  let v (k : Fin n) (p : LoopPlane) := xi p ^ 2 * u k p
  let dv (k : Fin n) (i : Fin 2) (p : LoopPlane) :=
    xi p ^ 2 * du k i p + 2 * xi p * dxi i p * u k p
  have hxic : HasCompactSupport (fun p => xi p ^ 2) :=
    hc.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset (g := fun t : ℝ => t ^ 2) (by simp) xi)
  have hxitop : MemLp (fun p => xi p ^ 2) ⊤ volume :=
    (hxi.continuous.pow 2).memLp_of_hasCompactSupport hxic
  have hdxi (i : Fin 2) : Continuous (dxi i) :=
    (hxi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdv (k : Fin n) (i : Fin 2) : MemLp (dv k i) 2 volume := by
    apply ((hdu k i).mul' hxitop).add
    exact (((continuous_const.mul hxi.continuous).mul (hdxi i)).mul (hu k)
      ).memLp_of_hasCompactSupport ((hc.mul_left.mul_right).mul_right)
  have hv (k : Fin n) : MemLp (v k) ⊤ volume :=
    ((hxi.continuous.pow 2).mul (hu k)).memLp_of_hasCompactSupport hxic.mul_right
  have hleft (k : Fin n) (i : Fin 2) : Integrable (fun p => F k i p * dv k i p) :=
    (hF k i).integrable_mul (hdv k i)
  have hright (k : Fin n) : Integrable (fun p => b k p * v k p) :=
    memLp_one_iff_integrable.mp ((hv k).mul' (memLp_one_iff_integrable.mpr (hb k)))
  let L := fun p => ∑ k, ∑ i, F k i p * dv k i p
  let T := fun p => ∑ k, b k p * v k p
  have hLI : Integrable L := integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun i _ => hleft k i
  have hTI : Integrable T := integrable_finsetSum _ fun k _ => hright k
  have hLT : (∫ p, L p) = ∫ p, T p := by
    rw [show L = fun p => ∑ k, ∑ i, F k i p * dv k i p from rfl,
      integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun i _ => hleft k i),
      show T = fun p => ∑ k, b k p * v k p from rfl,
      integral_finsetSum _ (fun k _ => hright k)]
    apply Finset.sum_congr rfl
    intro k _
    exact m64NaturalGrowth_mixed_cutoff_test (dirichlet k) hO (hF k) (hb k) (hu k)
      (hdu k) (hw k) (hz k) hxi hc hs (heq k)
  have hxiI : Integrable (fun p => xi p ^ 2) :=
    (hxi.continuous.pow 2).integrable_of_hasCompactSupport hxic
  have hpoint (p : LoopPlane) : nu / 2 * (H p * xi p ^ 2) ≤
      L p - T p + C0 * xi p ^ 2 +
        (4 * B ^ 2 * delta ^ 2 / nu) * (W p * ∑ i, dxi i p ^ 2) := by
    let Z := ∑ k, ∑ i, F k i p * u k p * dxi i p
    have hG : 0 ≤ ∑ i : Fin 2, dxi i p ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hHp := hH p
    have hWp := hW p
    have hyoung : 2 * (-(xi p * Z)) ≤ nu / 4 * (H p * xi p ^ 2) +
        (4 * B ^ 2 * delta ^ 2 / nu) * (W p * ∑ i, dxi i p ^ 2) := by
      apply two_mul_le_add_of_sq_le_mul (by positivity) (by positivity)
      calc
        (-(xi p * Z)) ^ 2 = xi p ^ 2 * Z ^ 2 := by ring
        _ ≤ xi p ^ 2 * (B ^ 2 * delta ^ 2 * H p * W p * ∑ i, dxi i p ^ 2) :=
          mul_le_mul_of_nonneg_left (hcross p) (sq_nonneg _)
        _ = _ := by field_simp
    have hc0 := mul_le_mul_of_nonneg_left (hcoercive p) (sq_nonneg (xi p))
    have hsrc := mul_le_mul_of_nonneg_left (hsource p) (sq_nonneg (xi p))
    have hsm := mul_le_mul_of_nonneg_right hsmall (mul_nonneg (hH p) (sq_nonneg (xi p)))
    have hL : L p = xi p ^ 2 * (∑ k, ∑ i, F k i p * du k i p) + 2 * xi p * Z := by
      simp only [L, dv, Z, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;>
        apply Finset.sum_congr rfl <;> intro i _ <;> ring
    have hT : T p = xi p ^ 2 * (∑ k, b k p * u k p) := by
      simp only [T, v, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hL, hT]
    nlinarith
  have hbound := integral_mono (hHI.const_mul (nu / 2))
    (((hLI.sub hTI).add (hxiI.const_mul C0)).add
      (hWI.const_mul (4 * B ^ 2 * delta ^ 2 / nu))) hpoint
  rw [integral_const_mul, integral_add' ((hLI.sub hTI).add (hxiI.const_mul C0))
      (hWI.const_mul (4 * B ^ 2 * delta ^ 2 / nu)),
    integral_add' (hLI.sub hTI) (hxiI.const_mul C0), integral_sub' hLI hTI,
    hLT, sub_self, zero_add, integral_const_mul, integral_const_mul] at hbound
  exact hbound

end PoincareConjecture
