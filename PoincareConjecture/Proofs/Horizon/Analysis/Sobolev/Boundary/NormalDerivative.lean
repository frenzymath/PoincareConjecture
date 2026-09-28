import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Coefficients
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Iterated.WeakDerivatives

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal

namespace Poincare.Analysis.Sobolev.BoundaryNormal

open Weak Poincare.Analysis.Sobolev.Euclidean NirenbergEuclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem partial_test_symmetric {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (i j : Fin d) (x : E) :
    fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) =
      fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1) := by
  have hd := (hφ.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  rw [fderiv_clm_apply (hd x) (differentiableAt_const _),
    fderiv_clm_apply (hd x) (differentiableAt_const _)]
  simpa using (hφ.contDiffAt.isSymmSndFDerivAt (by
    simp
    exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).eq
    (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)

private theorem weakPartial_commute {O : Set E} {u pi pj q : E → ℝ}
    (i j : Fin d) (hi : HasWeakPartialDeriv i pi u O)
    (hj : HasWeakPartialDeriv j pj u O) (hq : HasWeakPartialDeriv j q pi O) :
    HasWeakPartialDeriv i q pj O := by
  intro φ hφ hc hs
  let Di : E → ℝ := fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)
  let Dj : E → ℝ := fun x => fderiv ℝ φ x (EuclideanSpace.single j 1)
  have hDi : ContDiff ℝ ∞ Di :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hDj : ContDiff ℝ ∞ Dj :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have h1 := hj Di hDi (hc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans hs)
  have h2 := hi Dj hDj (hc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans hs)
  have heq : (∫ x in O, u x * fderiv ℝ Di x (EuclideanSpace.single j 1)) =
      ∫ x in O, u x * fderiv ℝ Dj x (EuclideanSpace.single i 1) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => congrArg (u x * ·) (partial_test_symmetric hφ i j x)
  have h3 := hq φ hφ hc hs
  change (∫ x in O, pj x * Di x) = -(∫ x in O, q x * φ x)
  linarith

private theorem memLp_coeff_mul {O : Set E} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) {a v : E → ℝ} (ha : Continuous a)
    (hv : MemLp v 2 (volume.restrict O)) :
    MemLp (fun x => a x * v x) 2 (volume.restrict O) := by
  obtain ⟨C, hC⟩ := hOc.exists_bound_of_continuousOn ha.continuousOn
  apply hv.of_le_mul (c := C) (ha.aestronglyMeasurable.mul hv.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x (subset_closure hx)) (norm_nonneg _)

private theorem weakPartial_sum {ι : Type*} (s : Finset ι) {O : Set E}
    {v q : ι → E → ℝ} (i : Fin d)
    (hv : ∀ j ∈ s, MemLp (v j) 2 (volume.restrict O))
    (hq : ∀ j ∈ s, MemLp (q j) 2 (volume.restrict O))
    (hw : ∀ j ∈ s, HasWeakPartialDeriv i (q j) (v j) O) :
    HasWeakPartialDeriv i (fun x => ∑ j ∈ s, q j x) (fun x => ∑ j ∈ s, v j x) O := by
  intro φ hφ hc hs
  have hφLp : MemLp φ 2 (volume.restrict O) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict O
  have hDLp : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2
      (volume.restrict O) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)).restrict O
  simp_rw [Finset.sum_mul]
  have hsumv := integral_finsetSum s (fun j hj => (hv j hj).integrable_mul hDLp)
  have hsumq := integral_finsetSum s (fun j hj => (hq j hj).integrable_mul hφLp)
  simp only [Pi.mul_apply] at hsumv hsumq
  rw [hsumv, hsumq, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j hj => hw j hj φ hφ hc hs

private theorem weakPartial_sub {O : Set E} {v w q r : E → ℝ} (i : Fin d)
    (hv : MemLp v 2 (volume.restrict O)) (hw : MemLp w 2 (volume.restrict O))
    (hq : MemLp q 2 (volume.restrict O)) (hr : MemLp r 2 (volume.restrict O))
    (hvq : HasWeakPartialDeriv i q v O) (hwr : HasWeakPartialDeriv i r w O) :
    HasWeakPartialDeriv i (fun x => q x - r x) (fun x => v x - w x) O := by
  intro φ hφ hc hs
  have hφLp : MemLp φ 2 (volume.restrict O) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict O
  have hDLp : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2
      (volume.restrict O) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)).restrict O
  simp_rw [sub_mul]
  have hsubv := integral_sub (hv.integrable_mul hDLp) (hw.integrable_mul hDLp)
  have hsubq := integral_sub (hq.integrable_mul hφLp) (hr.integrable_mul hφLp)
  simp only [Pi.mul_apply] at hsubv hsubq
  rw [hsubv, hsubq, hvq φ hφ hc hs, hwr φ hφ hc hs]
  ring

private theorem weakPartial_flux [NeZero d]
    (B : SmoothEllipticBilinearForm d univ) {O : Set E} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) {p : Fin d → E → ℝ}
    (hp : ∀ j, MemLp (p j) 2 (volume.restrict O)) (k i : Fin d)
    (hw : ∀ j, ∃ q, MemLp q 2 (volume.restrict O) ∧ HasWeakPartialDeriv k q (p j) O) :
    ∃ q, MemLp q 2 (volume.restrict O) ∧
      HasWeakPartialDeriv k q (fun x => ∑ j, B.a x i j * p j x) O := by
  choose q hq hwq using hw
  let r (j : Fin d) (x : E) := B.a x i j * q j x +
    fderiv ℝ (fun y => B.a y i j) x (EuclideanSpace.single k 1) * p j x
  have hr (j : Fin d) : MemLp (r j) 2 (volume.restrict O) :=
    (memLp_coeff_mul hO hOc (B.continuous_a i j) (hq j)).add
      (memLp_coeff_mul hO hOc
        (((B.smooth_a i j).continuous_fderiv (by simp)).clm_apply continuous_const) (hp j))
  refine ⟨fun x => ∑ j, r j x, memLp_finsetSum _ (fun j _ => hr j), ?_⟩
  apply weakPartial_sum Finset.univ k
    (fun j _ => memLp_coeff_mul hO hOc (B.continuous_a i j) (hp j))
    (fun j _ => hr j)
  intro j _
  exact (hwq j).mul_smooth hO (B.smooth_a i j)
    ((hp j).locallyIntegrable (by norm_num)) ((hq j).locallyIntegrable (by norm_num))

private theorem normal_flux_derivative [NeZero d] {O : Set E}
    {F : Fin d → E → ℝ} {f : E → ℝ}
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict O))
    (hf : MemLp f 2 (volume.restrict O))
    (ht : ∀ i : Fin d, i ≠ 0 →
      ∃ r, MemLp r 2 (volume.restrict O) ∧ HasWeakPartialDeriv i r (F i) O)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in O, f x * φ x) :
    ∃ r, MemLp r 2 (volume.restrict O) ∧ HasWeakPartialDeriv 0 r (F 0) O := by
  classical
  have hex (i : Fin d) : ∃ r, MemLp r 2 (volume.restrict O) ∧
      (i ≠ 0 → HasWeakPartialDeriv i r (F i) O) := by
    by_cases hi : i = 0
    · exact ⟨0, MemLp.zero, fun h => (h hi).elim⟩
    · obtain ⟨r, hr, hw⟩ := ht i hi
      exact ⟨r, hr, fun _ => hw⟩
  choose r hr hwr using hex
  let s : Finset (Fin d) := Finset.univ.erase 0
  let R : E → ℝ := fun x => -f x - ∑ i ∈ s, r i x
  have hsumr : MemLp (fun x => ∑ i ∈ s, r i x) 2 (volume.restrict O) :=
    memLp_finsetSum _ (fun i _ => hr i)
  refine ⟨R, hf.neg.sub hsumr, ?_⟩
  intro φ hφ hc hs
  have hφLp : MemLp φ 2 (volume.restrict O) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict O
  have hDLp (i : Fin d) : MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2
      (volume.restrict O) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)).restrict O
  have hmain := heq φ hφ hc hs
  have hsumF := integral_finsetSum Finset.univ (fun i _ => (hF i).integrable_mul (hDLp i))
  simp only [Pi.mul_apply] at hsumF
  rw [hsumF, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin d))] at hmain
  have htan : (∑ i ∈ s, ∫ x in O, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      -(∑ i ∈ s, ∫ x in O, r i x * φ x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact hwr i (Finset.ne_of_mem_erase hi) φ hφ hc hs
  change (∑ i ∈ s, ∫ x in O, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) +
    (∫ x in O, F 0 x * fderiv ℝ φ x (EuclideanSpace.single 0 1)) = _ at hmain
  rw [htan] at hmain
  have hR : (∫ x in O, R x * φ x) = -(∫ x in O, f x * φ x) -
      ∑ i ∈ s, ∫ x in O, r i x * φ x := by
    have hsub := integral_sub (hf.neg.integrable_mul hφLp) (hsumr.integrable_mul hφLp)
    have hsum := integral_finsetSum s (fun i _ => (hr i).integrable_mul hφLp)
    simp only [Pi.mul_apply, Pi.neg_apply] at hsub hsum
    dsimp only [R]
    simp_rw [sub_mul]
    rw [hsub]
    simp_rw [neg_mul, Finset.sum_mul]
    rw [integral_neg, hsum]
  rw [hR]
  linarith

private theorem normal_coefficient_pos [NeZero d]
    (B : SmoothEllipticBilinearForm d univ) (x : E) : 0 < B.a x 0 0 := by
  have h := B.coercive x (mem_univ x) (EuclideanSpace.single 0 1)
  have hbound : B.lam ≤ B.a x 0 0 := by
    simpa [matMulE, Matrix.mulVec, dotProduct, EuclideanSpace.inner_single_left] using h
  exact B.hlam_pos.trans_le hbound

theorem memWkp_two_of_tangential_weakDerivatives [NeZero d]
    (B : SmoothEllipticBilinearForm d univ) {O : Set E} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) {u f : E → ℝ} {p : Fin d → E → ℝ}
    (hu : MemLp u 2 (volume.restrict O)) (hf : MemLp f 2 (volume.restrict O))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict O))
    (hw : ∀ i, HasWeakPartialDeriv i (p i) u O)
    (htan : ∀ k : Fin d, k ≠ 0 → ∀ i : Fin d,
      ∃ q : E → ℝ, MemLp q 2 (volume.restrict O) ∧ HasWeakPartialDeriv k q (p i) O)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, B.a x i j * p j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) :
    MemWkp 2 2 u O := by
  classical
  have hother (i : Fin d) (hi : i ≠ 0) : MemW1p 2 (p i) O := by
    refine ⟨hp i, fun k => ?_⟩
    by_cases hk : k = 0
    · subst k
      obtain ⟨q, hq, hwq⟩ := htan i hi 0
      exact ⟨q, hq, weakPartial_commute 0 i (hw 0) (hw i) hwq⟩
    · exact htan k hk i
  let F (i : Fin d) (x : E) := ∑ j, B.a x i j * p j x
  have hF (i : Fin d) : MemLp (F i) 2 (volume.restrict O) :=
    memLp_finsetSum _ (fun j _ => memLp_coeff_mul hO hOc (B.continuous_a i j) (hp j))
  obtain ⟨r0, hr0, hw0⟩ := normal_flux_derivative hF hf
    (fun i hi => weakPartial_flux B hO hOc hp i i (htan i hi))
    (fun φ hφ hc hs => by simpa only [F, Finset.sum_mul] using heq φ hφ hc hs)
  have hex (j : Fin d) : ∃ q, MemLp q 2 (volume.restrict O) ∧
      (j ≠ 0 → HasWeakPartialDeriv 0 q (p j) O) := by
    by_cases hj : j = 0
    · exact ⟨0, MemLp.zero, fun h => (h hj).elim⟩
    · obtain ⟨q, hq, hwq⟩ := (hother j hj).2 0
      exact ⟨q, hq, fun _ => hwq⟩
  choose q hq hwq using hex
  let s : Finset (Fin d) := Finset.univ.erase 0
  let T : E → ℝ := fun x => ∑ j ∈ s, B.a x 0 j * p j x
  let r (j : Fin d) (x : E) := B.a x 0 j * q j x +
    fderiv ℝ (fun y => B.a y 0 j) x (EuclideanSpace.single 0 1) * p j x
  let rT : E → ℝ := fun x => ∑ j ∈ s, r j x
  have hT : MemLp T 2 (volume.restrict O) :=
    memLp_finsetSum _ (fun j _ => memLp_coeff_mul hO hOc (B.continuous_a 0 j) (hp j))
  have hr (j : Fin d) : MemLp (r j) 2 (volume.restrict O) :=
    (memLp_coeff_mul hO hOc (B.continuous_a 0 j) (hq j)).add
      (memLp_coeff_mul hO hOc
        (((B.smooth_a 0 j).continuous_fderiv (by simp)).clm_apply continuous_const) (hp j))
  have hrT : MemLp rT 2 (volume.restrict O) := memLp_finsetSum _ (fun j _ => hr j)
  have hwT : HasWeakPartialDeriv 0 rT T O := by
    apply weakPartial_sum s 0
      (fun j _ => memLp_coeff_mul hO hOc (B.continuous_a 0 j) (hp j)) (fun j _ => hr j)
    intro j hj
    exact (hwq j (Finset.ne_of_mem_erase hj)).mul_smooth hO (B.smooth_a 0 j)
      ((hp j).locallyIntegrable (by norm_num)) ((hq j).locallyIntegrable (by norm_num))
  have hweighted := weakPartial_sub 0 (hF 0) hT hr0 hrT hw0 hwT
  have hFT : (fun x => F 0 x - T x) = fun x => B.a x 0 0 * p 0 x := by
    funext x
    dsimp only [F, T, s]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin d))]
    ring
  rw [hFT] at hweighted
  let a : E → ℝ := fun x => (B.a x 0 0)⁻¹
  have ha : ContDiff ℝ ∞ a := (B.smooth_a 0 0).inv (fun x => (normal_coefficient_pos B x).ne')
  have hval : MemLp (fun x => B.a x 0 0 * p 0 x) 2 (volume.restrict O) :=
    memLp_coeff_mul hO hOc (B.continuous_a 0 0) (hp 0)
  have hdiff : MemLp (fun x => r0 x - rT x) 2 (volume.restrict O) := hr0.sub hrT
  let q0 : E → ℝ := fun x => a x * (r0 x - rT x) +
    fderiv ℝ a x (EuclideanSpace.single 0 1) * (B.a x 0 0 * p 0 x)
  have hq0 : MemLp q0 2 (volume.restrict O) :=
    (memLp_coeff_mul hO hOc ha.continuous hdiff).add
      (memLp_coeff_mul hO hOc ((ha.continuous_fderiv (by simp)).clm_apply continuous_const) hval)
  have hwq0 : HasWeakPartialDeriv 0 q0 (p 0) O := by
    have hv := hweighted.mul_smooth hO ha
      (hval.locallyIntegrable (by norm_num)) (hdiff.locallyIntegrable (by norm_num))
    have hvfun : (fun x => a x * (B.a x 0 0 * p 0 x)) = p 0 := by
      funext x
      dsimp only [a]
      rw [← mul_assoc, inv_mul_cancel₀ (normal_coefficient_pos B x).ne', one_mul]
    rw [hvfun] at hv
    exact hv
  apply memWkp_succ_of_weakDerivatives hO (by norm_num : (1 : ℝ≥0∞) ≤ 2) hu (g := p)
  · intro i
    apply MemWkp.one_iff_memW1p.mpr
    by_cases hi : i = 0
    · subst i
      refine ⟨hp 0, fun k => ?_⟩
      by_cases hk : k = 0
      · subst k
        exact ⟨q0, hq0, hwq0⟩
      · exact htan k hk 0
    · exact hother i hi
  · exact hw

end Poincare.Analysis.Sobolev.BoundaryNormal
