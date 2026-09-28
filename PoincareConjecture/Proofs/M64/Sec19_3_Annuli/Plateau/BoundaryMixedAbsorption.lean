import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryMixedTests

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak

namespace PoincareConjecture

set_option maxHeartbeats 1200000 in

theorem m64NaturalGrowth_mixed_diffQuot_absorb
    {n : ℕ} (dirichlet : Fin n → Prop)
    {O : Set LoopPlane} (hO : IsOpen O)
    {F du : Fin n → Fin 2 → LoopPlane → ℝ} {b u : Fin n → LoopPlane → ℝ}
    {xi H W : LoopPlane → ℝ} {nu B kappa : ℝ}
    (hnu : 0 < nu) (hB : 0 ≤ B) (hk : 0 ≤ kappa) (hsmall : 2 * B * kappa ≤ nu / 2)
    (hH : Integrable H) (hW : MemLp W ⊤ volume) (hW0 : ∀ x, 0 ≤ W x)
    (hF : ∀ a i, MemLp (F a i) 2 volume) (hb : ∀ a, Integrable (b a))
    (hu : ∀ a, Continuous (u a)) (hdu : ∀ a i, MemLp (du a i) 2 volume)
    (hw : ∀ a i, HasWeakPartialDeriv i (du a i) (u a) univ)
    (hz : ∀ a, dirichlet a → ∀ x : LoopPlane, x 1 < 0 → u a x = 0)
    (hxi : ContDiff ℝ ∞ xi) (hc : HasCompactSupport xi) (hs : tsupport xi ⊆ O)
    (heq : ∀ a (phi : LoopPlane → ℝ), ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O → (dirichlet a → ∀ x : LoopPlane, x 1 = 0 → phi x = 0) →
      (∫ x, ∑ i : Fin 2, F a i x * fderiv ℝ phi x (EuclideanSpace.single i 1)) =
        ∫ x, b a x * phi x)
    (hpot : ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O → (∫ x, H x * phi x ^ 2) ≤ kappa *
        ∫ x, W x * ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2)
    {h : ℝ} (hh : h ≠ 0) (hsupp : cthickening |h| (tsupport xi) ⊆ O)
    (hpoint : ∀ x,
      nu * (W x * ∑ a : Fin n, ∑ i : Fin 2, (xi x * diffQuot 0 h (du a i) x) ^ 2) ≤
        (∑ a : Fin n, ∑ i : Fin 2, diffQuot 0 h (F a i) x *
          (xi x ^ 2 * diffQuot 0 h (du a i) x + 2 * xi x *
            fderiv ℝ xi x (EuclideanSpace.single i 1) * diffQuot 0 h (u a) x)) -
        (∑ a : Fin n, diffQuot 0 h (b a) x * (xi x ^ 2 * diffQuot 0 h (u a) x)) +
        B * ((H x * xi x ^ 2 + ∑ a : Fin n, H x * (xi x * diffQuot 0 h (u a) x) ^ 2) +
          W x * ∑ a : Fin n, ∑ i : Fin 2,
            (fderiv ℝ xi x (EuclideanSpace.single i 1) * diffQuot 0 h (u a) x) ^ 2)) :
    (∫ x, W x * ∑ a : Fin n, ∑ i : Fin 2, (xi x * diffQuot 0 h (du a i) x) ^ 2) ≤
      (2 * B / nu) * ((∫ x, H x * xi x ^ 2) + (1 + 2 * kappa) *
        ∫ x, W x * ∑ a : Fin n, ∑ i : Fin 2,
          (fderiv ℝ xi x (EuclideanSpace.single i 1) * diffQuot 0 h (u a) x) ^ 2) := by
  let dxi (i : Fin 2) (x : LoopPlane) := fderiv ℝ xi x (EuclideanSpace.single i 1)
  let U (a : Fin n) := diffQuot 0 h (u a)
  let A (a : Fin n) (i : Fin 2) (x : LoopPlane) := xi x * diffQuot 0 h (du a i) x
  let J (a : Fin n) (i : Fin 2) (x : LoopPlane) := dxi i x * U a x
  let V (a : Fin n) (x : LoopPlane) := xi x ^ 2 * U a x
  let DV (a : Fin n) (i : Fin 2) (x : LoopPlane) :=
    xi x ^ 2 * diffQuot 0 h (du a i) x + 2 * xi x * dxi i x * U a x
  have hUc (a : Fin n) : Continuous (U a) := continuous_diffQuot_of_continuous 0 h (hu a)
  have hAc (a : Fin n) (i : Fin 2) : MemLp (A a i) 2 volume :=
    (M60.suWeakMap_diffQuot_memLp (hdu a i) 0 h).mul'
      (hxi.continuous.memLp_of_hasCompactSupport hc : MemLp xi ⊤ volume)
  have hJc (a : Fin n) (i : Fin 2) : MemLp (J a i) 2 volume :=
    (((hxi.continuous_fderiv (by simp)).clm_apply continuous_const).mul (hUc a)
      ).memLp_of_hasCompactSupport ((hc.fderiv_apply (𝕜 := ℝ) _).mul_right)
  have hxic : HasCompactSupport (fun x => xi x ^ 2) :=
    hc.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset (g := fun s : ℝ => s ^ 2) (by simp) xi)
  have hV (a : Fin n) : MemLp (V a) ⊤ volume :=
    ((hxi.continuous.pow 2).mul (hUc a)).memLp_of_hasCompactSupport hxic.mul_right
  have hDV (a : Fin n) (i : Fin 2) : MemLp (DV a i) 2 volume := by
    have hf : MemLp (fun x => xi x * A a i x) 2 volume := (hAc a i).mul'
      (hxi.continuous.memLp_of_hasCompactSupport hc : MemLp xi ⊤ volume)
    have hg : MemLp (fun x => (2 * xi x) * J a i x) 2 volume := (hJc a i).mul'
      ((continuous_const.mul hxi.continuous).memLp_of_hasCompactSupport hc.mul_left :
        MemLp (fun x => 2 * xi x) ⊤ volume)
    convert hf.add hg using 1
    funext x
    dsimp only [A, J, DV, Pi.add_apply]
    ring
  have hsquare {v : LoopPlane → ℝ} (hv : MemLp v 2 volume) :
      Integrable (fun x => W x * v x ^ 2) := by
    have hsq : MemLp (fun x => v x ^ 2) 1 volume := by simpa only [pow_two] using hv.mul' hv
    exact memLp_one_iff_integrable.mp (hsq.mul' hW)
  have hweighted (f : Fin n → Fin 2 → LoopPlane → ℝ) (hf : ∀ a i, MemLp (f a i) 2 volume) :
      Integrable (fun x => W x * ∑ a : Fin n, ∑ i : Fin 2, f a i x ^ 2) := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun a _ =>
      integrable_finsetSum _ fun i _ => hsquare (hf a i)
  have hAI := hweighted A hAc
  have hJI := hweighted J hJc
  have hPI (a : Fin n) : Integrable (fun x => H x * (xi x * U a x) ^ 2) := by
    have hcont := (hxi.continuous.mul (hUc a)).pow 2
    have hsupp : HasCompactSupport (fun x => (xi x * U a x) ^ 2) :=
      hc.mul_right.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_comp_subset (g := fun s : ℝ => s ^ 2) (by simp) (fun x => xi x * U a x))
    exact memLp_one_iff_integrable.mp
      ((hcont.memLp_of_hasCompactSupport hsupp : MemLp _ ⊤ volume).mul'
        (memLp_one_iff_integrable.mpr hH))
  have hKI : Integrable (fun x => H x * xi x ^ 2) :=
    memLp_one_iff_integrable.mp
      (((hxi.continuous.pow 2).memLp_of_hasCompactSupport hxic : MemLp _ ⊤ volume).mul'
        (memLp_one_iff_integrable.mpr hH))
  let L (x : LoopPlane) := ∑ a : Fin n, ∑ i : Fin 2, diffQuot 0 h (F a i) x * DV a i x
  let T (x : LoopPlane) := ∑ a : Fin n, diffQuot 0 h (b a) x * V a x
  have hLI : Integrable L := integrable_finsetSum _ fun a _ =>
    integrable_finsetSum _ fun i _ => memLp_one_iff_integrable.mp
      ((hDV a i).mul' (M60.suWeakMap_diffQuot_memLp (hF a i) 0 h))
  have hTI : Integrable T := integrable_finsetSum _ fun a _ =>
    memLp_one_iff_integrable.mp ((hV a).mul'
      (M60.suWeakMap_diffQuot_memLp (memLp_one_iff_integrable.mpr (hb a)) 0 h))
  have hequal : (∫ x, L x) = ∫ x, T x := by
    rw [show L = fun x => ∑ a : Fin n, ∑ i : Fin 2,
        diffQuot 0 h (F a i) x * DV a i x from rfl,
      integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun i _ =>
        memLp_one_iff_integrable.mp ((hDV a i).mul'
          (M60.suWeakMap_diffQuot_memLp (hF a i) 0 h))),
      show T = fun x => ∑ a : Fin n, diffQuot 0 h (b a) x * V a x from rfl,
      integral_finsetSum _ (fun a _ => memLp_one_iff_integrable.mp ((hV a).mul'
        (M60.suWeakMap_diffQuot_memLp (memLp_one_iff_integrable.mpr (hb a)) 0 h)))]
    apply Finset.sum_congr rfl
    intro a _
    exact m64NaturalGrowth_mixed_nirenberg_identity (dirichlet a) hO (hF a) (hb a)
      (hu a) (hdu a) (hw a) (hz a) hxi hc (heq a) hh hsupp
  have hpotential := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin n))) =>
    M60.suWeightedPotential_diffQuot_bound (p := 2) (t := 1)
      (by norm_num) (by norm_num) hO hk hH hW hW0
      (hu a) (hdu a) (hw a) hxi hc hs hpot 0 h)
  have hsumW (f : Fin n → Fin 2 → LoopPlane → ℝ) (hf : ∀ a i, MemLp (f a i) 2 volume) :
      (∫ x, W x * ∑ a : Fin n, ∑ i : Fin 2, f a i x ^ 2) =
        ∑ a : Fin n, ∫ x, W x * ∑ i : Fin 2, f a i x ^ 2 := by
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum _ fun a _ => integrable_finsetSum _ fun i _ => hsquare (hf a i)
  have hpotential' : (∫ x, ∑ a : Fin n, H x * (xi x * U a x) ^ 2) ≤
      2 * kappa * ((∫ x, W x * ∑ a : Fin n, ∑ i : Fin 2, A a i x ^ 2) +
        ∫ x, W x * ∑ a : Fin n, ∑ i : Fin 2, J a i x ^ 2) := by
    rw [integral_finsetSum _ (fun a _ => hPI a), hsumW A hAc, hsumW J hJc]
    simpa only [U, A, J, dxi, mul_add, Finset.mul_sum, Finset.sum_add_distrib] using hpotential
  have hmain := integral_mono (hAI.const_mul nu)
    ((hLI.sub hTI).add ((hKI.add (integrable_finsetSum _ (fun a _ => hPI a))
      |>.add hJI).const_mul B)) hpoint
  rw [integral_const_mul, integral_add' (hLI.sub hTI)
      (((hKI.add (integrable_finsetSum _ (fun a _ => hPI a))).add hJI).const_mul B),
    integral_sub' hLI hTI, hequal, sub_self, zero_add, integral_const_mul,
    integral_add' (hKI.add (integrable_finsetSum _ (fun a _ => hPI a))) hJI,
    integral_add' hKI (integrable_finsetSum _ (fun a _ => hPI a))] at hmain
  have hI0 : 0 ≤ ∫ x, W x * ∑ a : Fin n, ∑ i : Fin 2, A a i x ^ 2 :=
    integral_nonneg fun x => mul_nonneg (hW0 x)
      (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hsm := mul_le_mul_of_nonneg_right hsmall hI0
  have hpB := mul_le_mul_of_nonneg_left hpotential' hB
  change (∫ x, W x * ∑ a : Fin n, ∑ i : Fin 2, A a i x ^ 2) ≤
    (2 * B / nu) * ((∫ x, H x * xi x ^ 2) + (1 + 2 * kappa) *
      ∫ x, W x * ∑ a : Fin n, ∑ i : Fin 2, J a i x ^ 2)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hnu).mpr
  nlinarith

end PoincareConjecture
