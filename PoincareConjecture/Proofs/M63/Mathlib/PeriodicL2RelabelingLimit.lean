import PoincareConjecture.Proofs.M63.Mathlib.PeriodicL2Relabeling
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicL2UniformLimit
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.Normed.Group.Quotient










set_option autoImplicit false

open MeasureTheory AddCircle Filter Set
open scoped NNReal ENNReal Topology intervalIntegral

namespace PoincareConjecture.M63




theorem cauchySeq_periodic_comp_of_cauchySeq_L2
    {L : ℝ} [Fact (0 < L)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f h : ℕ → C(AddCircle L, E)) (psi : ℕ → ℝ → ℝ)
    {ell : ℝ} (hell : 0 < ell) {k : ℝ≥0}
    (hpsi : ∀ j, ContDiff ℝ 1 (psi j))
    (hshift : ∀ j x, psi j (x + L) = psi j x + L)
    (hderiv : ∀ j x, ell ≤ deriv (psi j) x)
    (hlabels : ∀ eps : ℝ, 0 < eps → ∃ N : ℕ,
      ∀ j ≥ N, ∀ m ≥ N, ∀ x ∈ Icc 0 L, |psi j x - psi m x| < eps)
    (hL2 : CauchySeq (fun j =>
      ContinuousMap.toLp 2 (haarAddCircle (T := L)) ℝ (f j)))
    (hcomp : ∀ (j : ℕ) (x : ℝ), h j (x : AddCircle L) =
      f j (psi j x : AddCircle L))
    (hLip : ∀ j, LipschitzWith k (fun x : ℝ => h j (x : AddCircle L))) :
    CauchySeq h := by
  classical
  have hL : 0 < L := Fact.out
  let T : C(AddCircle L, E) →L[ℝ] Lp E 2 (haarAddCircle (T := L)) :=
    ContinuousMap.toLp 2 haarAddCircle ℝ
  have hp (j : ℕ) : Function.Periodic (fun x : ℝ => (psi j x : AddCircle L)) L := by
    intro x
    change (psi j (x + L) : AddCircle L) = (psi j x : AddCircle L)
    rw [hshift j, AddCircle.coe_add_period]
  let Phi (j : ℕ) : C(AddCircle L, AddCircle L) :=
    ⟨(hp j).lift,
      (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L)).continuous_iff.mpr
        ((AddCircle.continuous_mk' L).comp (hpsi j).continuous)⟩
  have hPhi (j : ℕ) (x : ℝ) : Phi j (x : AddCircle L) = (psi j x : AddCircle L) :=
    Function.Periodic.lift_coe (hp j) x
  have hident (j : ℕ) : h j = (f j).comp (Phi j) := by
    ext z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    change h j (x : AddCircle L) = f j (Phi j (x : AddCircle L))
    rw [hPhi]
    exact hcomp j x
  have hnorm (u : C(AddCircle L, E)) :
      ‖T u‖ ^ 2 = ∫ z : AddCircle L, ‖u z‖ ^ 2 ∂haarAddCircle := by
    rw [Lp.norm_def, eLpNorm_congr_ae
      (ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℝ) u),
      toReal_eLpNorm (u.memLp (p := 2) (μ := haarAddCircle) ℝ).1,
      lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
        (u.memLp (p := 2) (μ := haarAddCircle) ℝ).1]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, inv_eq_one_div, ← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  have hperiod (u : C(AddCircle L, E)) :
      Function.Periodic (fun x : ℝ => u (x : AddCircle L)) L := by
    intro x
    change u ((x + L : ℝ) : AddCircle L) = u (x : AddCircle L)
    rw [AddCircle.coe_add_period]
  have hintegral (u : C(AddCircle L, E)) :
      (∫ z : AddCircle L, ‖u z‖ ^ 2 ∂haarAddCircle) =
        L⁻¹ * ∫ x in (0 : ℝ)..L, ‖u (x : AddCircle L)‖ ^ 2 := by
    rw [integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage L 0]
    simp only [zero_add, smul_eq_mul]
  have hsq (j : ℕ) (u : C(AddCircle L, E)) :
      ‖T (u.comp (Phi j))‖ ^ 2 ≤ ell⁻¹ * ‖T u‖ ^ 2 := by
    have hsub := (hperiod u).integral_norm_sq_comp_le
      (u.continuous.comp (AddCircle.continuous_mk' L)) hL
      (hpsi j) (hshift j) hell (hderiv j)
    rw [hnorm, hnorm, hintegral, hintegral]
    calc
      _ = L⁻¹ * ∫ x in (0 : ℝ)..L, ‖u (psi j x : AddCircle L)‖ ^ 2 := rfl
      _ ≤ L⁻¹ * (ell⁻¹ * ∫ x in (0 : ℝ)..L, ‖u (x : AddCircle L)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr hL.le)
      _ = _ := by ring
  let C : ℝ := Real.sqrt ell⁻¹
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hbound (j : ℕ) (u : C(AddCircle L, E)) :
      ‖T (u.comp (Phi j))‖ ≤ C * ‖T u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr hell.le)]
    exact hsq j u
  have hcontract (u : C(AddCircle L, E)) : ‖T u‖ ≤ ‖u‖ := by
    have hT : ‖T‖ ≤ 1 := by
      simpa [T, measureUnivNNReal] using
        (ContinuousMap.toLp_norm_le (p := 2) (𝕜 := ℝ) (E := E) haarAddCircle)
    calc
      _ ≤ ‖T‖ * ‖u‖ := T.le_opNorm u
      _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg u)
      _ = ‖u‖ := one_mul _
  apply cauchySeq_of_cauchySeq_L2_of_lipschitz h _ hLip
  apply Metric.cauchySeq_iff.mpr
  intro eps heps
  let d : ℝ := eps / (8 * (C + 1))
  have hd : 0 < d := by dsimp [d]; positivity
  have hdeq : 8 * (C + 1) * d = eps := by dsimp [d]; field_simp
  have hsmall : C * d < eps / 4 := by nlinarith [mul_nonneg hC hd.le]
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hL2 d hd
  obtain ⟨eta, heta, hcont⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous (f N).continuous)
    (eps / 4) (by positivity)
  obtain ⟨M, hM⟩ := hlabels eta heta
  refine ⟨max N M, fun j hj m hm => ?_⟩
  have hjN : N ≤ j := (le_max_left N M).trans hj
  have hmN : N ≤ m := (le_max_left N M).trans hm
  have hjM : M ≤ j := (le_max_right N M).trans hj
  have hmM : M ≤ m := (le_max_right N M).trans hm
  have hleft : ‖T ((f j - f N).comp (Phi j))‖ < eps / 4 := by
    have hn : ‖T (f j - f N)‖ < d := by
      simpa only [T, map_sub, dist_eq_norm] using hN j hjN N le_rfl
    exact (hbound j _).trans_lt
      ((mul_le_mul_of_nonneg_left hn.le hC).trans_lt hsmall)
  have hright : ‖T ((f N - f m).comp (Phi m))‖ < eps / 4 := by
    have hn : ‖T (f N - f m)‖ < d := by
      simpa only [T, map_sub, dist_eq_norm] using hN N le_rfl m hmN
    exact (hbound m _).trans_lt
      ((mul_le_mul_of_nonneg_left hn.le hC).trans_lt hsmall)
  have hmiddle : ‖T ((f N).comp (Phi j) - (f N).comp (Phi m))‖ ≤ eps / 4 := by
    apply (hcontract _).trans
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro z
    let x : ℝ := equivIco L 0 z
    have hx : x ∈ Icc 0 L := by
      have hx' := (equivIco L 0 z).property
      exact ⟨hx'.1, by simpa only [zero_add] using hx'.2.le⟩
    have hz : (x : AddCircle L) = z := coe_equivIco
    rw [← hz]
    change ‖f N (Phi j (x : AddCircle L)) - f N (Phi m (x : AddCircle L))‖ ≤ _
    rw [hPhi, hPhi]
    have hdist : dist (psi j x : AddCircle L) (psi m x : AddCircle L) < eta := by
      calc
        _ = ‖((psi j x - psi m x : ℝ) : AddCircle L)‖ := by
          rw [dist_eq_norm, QuotientAddGroup.mk_sub]
        _ ≤ ‖psi j x - psi m x‖ := QuotientAddGroup.norm_mk_le_norm
        _ < eta := by simpa only [Real.norm_eq_abs] using hM j hjM m hmM x hx
    exact (by simpa only [dist_eq_norm] using (hcont hdist).le)
  have hdecomp : h j - h m = (f j - f N).comp (Phi j) +
      ((f N).comp (Phi j) - (f N).comp (Phi m)) + (f N - f m).comp (Phi m) := by
    rw [hident j, hident m]
    ext z
    change f j (Phi j z) - f m (Phi m z) =
      (f j (Phi j z) - f N (Phi j z)) +
        (f N (Phi j z) - f N (Phi m z)) + (f N (Phi m z) - f m (Phi m z))
    abel
  change dist (T (h j)) (T (h m)) < eps
  rw [dist_eq_norm, ← map_sub, hdecomp, map_add, map_add]
  have htri1 := norm_add_le
    (T ((f j - f N).comp (Phi j)) + T ((f N).comp (Phi j) - (f N).comp (Phi m)))
    (T ((f N - f m).comp (Phi m)))
  have htri2 := norm_add_le (T ((f j - f N).comp (Phi j)))
    (T ((f N).comp (Phi j) - (f N).comp (Phi m)))
  linarith

end PoincareConjecture.M63
