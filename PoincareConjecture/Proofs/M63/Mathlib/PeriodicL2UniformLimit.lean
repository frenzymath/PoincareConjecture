import PoincareConjecture.Proofs.M63.Mathlib.PeriodicGaussianLipschitz
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicL2Heat
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

open MeasureTheory AddCircle Filter
open scoped NNReal ENNReal Topology

namespace PoincareConjecture.M63

theorem cauchySeq_of_cauchySeq_L2_of_lipschitz
    {L : ℝ} [Fact (0 < L)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : ℕ → C(AddCircle L, E)) {k : ℝ≥0}
    (hL2 : CauchySeq (fun j =>
      ContinuousMap.toLp 2 (haarAddCircle (T := L)) ℝ (f j)))
    (hLip : ∀ j, LipschitzWith k (fun x : ℝ => f j (x : AddCircle L))) :
    CauchySeq f := by
  classical
  have hcomplex (g : ℕ → C(AddCircle L, ℂ)) (r : ℝ≥0)
      (hLp : CauchySeq (fun j => ContinuousMap.toLp 2 haarAddCircle ℝ (g j)))
      (hG : ∀ j, LipschitzWith r (fun x : ℝ => g j (x : AddCircle L))) :
      CauchySeq g := by
    have hscalar (u : C(AddCircle L, ℂ)) :
        ContinuousMap.toLp 2 haarAddCircle ℝ u = ContinuousMap.toLp 2 haarAddCircle ℂ u := by
      apply Lp.ext
      exact (ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℝ) u).trans
        (ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℂ) u).symm
    have hLp' : CauchySeq (fun j => ContinuousMap.toLp 2 haarAddCircle ℂ (g j)) := by
      simpa only [hscalar] using hLp
    apply Metric.cauchySeq_iff.mpr
    intro eps heps
    let C : ℝ := (r : ℝ) * ∫ z : ℝ, ‖(-2 * z) * gaussianHeatKernel 1 z‖
    have hC : 0 ≤ C := mul_nonneg r.coe_nonneg (integral_nonneg fun _ => norm_nonneg _)
    let d : ℝ := eps / (8 * (C + 1))
    have hd : 0 < d := by dsimp [d]; positivity
    have hdeq : 8 * (C + 1) * d = eps := by
      dsimp [d]
      field_simp
    have herror : C * Real.sqrt (d ^ 2) < eps / 4 := by
      rw [Real.sqrt_sq hd.le]
      nlinarith [mul_nonneg hC hd.le]
    have htime : 0 < d ^ 2 := sq_pos_of_pos hd
    have hsmooth := (periodicL2Heat (L := L) (d ^ 2) htime).lipschitz.cauchySeq_comp hLp'
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hsmooth (eps / 2) (by positivity)
    refine ⟨N, fun j hj m hm => ?_⟩
    have hleft := (periodicGaussianHeat_lipschitz_error_bound (g j) (hG j)
      (sq_nonneg d)).trans_lt herror
    have hright := (periodicGaussianHeat_lipschitz_error_bound (g m) (hG m)
      (sq_nonneg d)).trans_lt herror
    have hmid : dist (periodicGaussianHeat (d ^ 2) (g j))
        (periodicGaussianHeat (d ^ 2) (g m)) < eps / 2 := by
      simpa only [Function.comp_def, periodicL2Heat_eq_gaussian] using hN j hj m hm
    rw [← dist_eq_norm] at hleft hright
    have htri1 := dist_triangle (g j) (periodicGaussianHeat (d ^ 2) (g j)) (g m)
    have htri2 := dist_triangle (periodicGaussianHeat (d ^ 2) (g j))
      (periodicGaussianHeat (d ^ 2) (g m)) (g m)
    rw [dist_comm (periodicGaussianHeat (d ^ 2) (g j)) (g j)] at hleft
    linarith
  let Q := (Module.finBasis ℝ E).equivFunL
  let A (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp ((ContinuousLinearMap.proj i).comp Q.toContinuousLinearMap)
  let g (i : Fin (Module.finrank ℝ E)) (j : ℕ) : C(AddCircle L, ℂ) :=
    (A i).compLeftContinuous ℝ (AddCircle L) (f j)
  have hmap (i : Fin (Module.finrank ℝ E)) (j : ℕ) :
      (A i).compLpL 2 haarAddCircle (ContinuousMap.toLp 2 haarAddCircle ℝ (f j)) =
        ContinuousMap.toLp 2 haarAddCircle ℝ (g i j) := by
    apply Lp.ext
    filter_upwards [(A i).coeFn_compLpL (ContinuousMap.toLp 2 haarAddCircle ℝ (f j)),
      ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℝ) (f j),
      ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℝ) (g i j)] with x hx hy hz
    rw [hx, hy, hz]
    rfl
  have hcoord (i : Fin (Module.finrank ℝ E)) : CauchySeq (g i) := by
    apply hcomplex (g i) (‖A i‖₊ * k)
    · have h := ((A i).compLpL 2 haarAddCircle).lipschitz.cauchySeq_comp hL2
      simpa only [Function.comp_def, hmap] using h
    · intro j
      exact (A i).lipschitz.comp (hLip j)
  apply Metric.cauchySeq_iff.mpr
  intro eps heps
  let B : ℝ := ‖Q.symm.toContinuousLinearMap‖
  have hB : 0 ≤ B := norm_nonneg _
  let d : ℝ := eps / (2 * (B + 1))
  have hd : 0 < d := by dsimp [d]; positivity
  have hdeq : 2 * (B + 1) * d = eps := by dsimp [d]; field_simp
  have hsmall : B * d < eps := by nlinarith [mul_nonneg hB hd.le]
  choose N hN using fun i => Metric.cauchySeq_iff.mp (hcoord i) d hd
  refine ⟨Finset.univ.sup N, fun j hj m hm => ?_⟩
  have hpoint (x : AddCircle L) : ‖Q (f j x - f m x)‖ ≤ d := by
    apply (pi_norm_le_iff_of_nonneg hd.le).mpr
    intro i
    have hni : N i ≤ Finset.univ.sup N := Finset.le_sup (Finset.mem_univ i)
    have hi := hN i j (hni.trans hj) m (hni.trans hm)
    rw [dist_eq_norm] at hi
    calc
      _ = ‖(g i j - g i m) x‖ := by
        change ‖Q (f j x - f m x) i‖ =
          ‖((Q (f j x) i : ℝ) : ℂ) - ((Q (f m x) i : ℝ) : ℂ)‖
        rw [← Complex.ofReal_sub, Complex.norm_real, map_sub]
        rfl
      _ ≤ ‖g i j - g i m‖ := ContinuousMap.norm_coe_le_norm _ _
      _ ≤ d := hi.le
  have hnorm : ‖f j - f m‖ ≤ B * d := by
    apply (ContinuousMap.norm_le _ (mul_nonneg hB hd.le)).mpr
    intro x
    change ‖f j x - f m x‖ ≤ _
    calc
      _ = ‖Q.symm (Q (f j x - f m x))‖ := by rw [Q.symm_apply_apply]
      _ ≤ B * ‖Q (f j x - f m x)‖ := Q.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ B * d := mul_le_mul_of_nonneg_left (hpoint x) hB
  exact (by simpa only [dist_eq_norm] using hnorm.trans_lt hsmall)

end PoincareConjecture.M63
