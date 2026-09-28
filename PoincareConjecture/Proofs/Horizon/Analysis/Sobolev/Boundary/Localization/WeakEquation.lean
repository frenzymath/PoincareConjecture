import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Localization.Sobolev







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff ENNReal

namespace Poincare.Analysis.Sobolev.BoundaryLocalization

open Weak Poincare.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem memWkp_sum {O : Set E} (hO : IsOpen O) (k : ℕ)
    {ι : Type*} (s : Finset ι) {v : ι → E → ℝ}
    (hv : ∀ i ∈ s, MemWkp k 2 (v i) O) :
    MemWkp k 2 (fun x => ∑ i ∈ s, v i x) O := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (MemWkp_zero_fun (d := d) (k := k) (by norm_num) hO)
  | @insert a s ha ih =>
    simpa only [Finset.sum_insert ha] using
      MemWkp.add (by norm_num) hO (hv a (Finset.mem_insert_self a s))
        (ih (fun i hi => hv i (Finset.mem_insert_of_mem hi)))

private theorem integral_sum_sum {O : Set E} {v : Fin d → Fin d → E → ℝ}
    (hv : ∀ i j, Integrable (v i j) (volume.restrict O)) :
    (∫ x in O, ∑ i, ∑ j, v i j x) = ∑ i, ∑ j, ∫ x in O, v i j x := by
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hv i j))]
  exact Finset.sum_congr rfl fun i _ => integral_finsetSum Finset.univ (fun j _ => hv i j)

private theorem integral_inter_eq {W O : Set E} (hW : IsOpen W) {v : E → ℝ}
    (hv : ∀ x, x ∉ W → v x = 0) :
    (∫ x in W ∩ O, v x) = ∫ x in O, v x := by
  rw [← Measure.restrict_restrict hW.measurableSet]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hv



theorem localize_weak_divergence
    (k : ℕ) {O W : Set E} (hO : IsOpen O) (hW : IsOpen W)
    (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {u f χ : E → ℝ} (hu : MemWkp (k + 1) 2 u (W ∩ O))
    (hf : MemWkp k 2 f (W ∩ O))
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ W)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ W ∩ O →
      (∫ x in W ∩ O, ∑ i, ∑ j, a x i j * chosenWeakPartial' 2 j u (W ∩ O) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in W ∩ O, f x * φ x) :
    let p := fun j => chosenWeakPartial' 2 j u (W ∩ O)
    let F := fun x => χ x * f x - ∑ i, ∑ j,
      (fderiv ℝ (fun y => a y i j * fderiv ℝ χ y (EuclideanSpace.single j 1)) x
          (EuclideanSpace.single i 1) * u x +
        a x i j * fderiv ℝ χ x (EuclideanSpace.single j 1) * p i x +
        a x i j * p j x * fderiv ℝ χ x (EuclideanSpace.single i 1))
    MemWkp k 2 F O ∧
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
        (∫ x in O, ∑ i, ∑ j, a x i j *
          chosenWeakPartial' 2 j (fun y => χ y * u y) O x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, F x * φ x := by
  classical
  let p (j : Fin d) := chosenWeakPartial' 2 j u (W ∩ O)
  let Dχ (j : Fin d) (x : E) := fderiv ℝ χ x (EuclideanSpace.single j 1)
  have hp (j : Fin d) : MemWkp k 2 (p j) (W ∩ O) := hu.chosenWeakPartial_mem j
  have hw (j : Fin d) : HasWeakPartialDeriv j (p j) u (W ∩ O) :=
    chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p j
  have hDχ (j : Fin d) : ContDiff ℝ ∞ (Dχ j) :=
    (hχ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hDχc (j : Fin d) : HasCompactSupport (Dχ j) := hc.fderiv_apply ℝ _
  have hDχs (j : Fin d) : tsupport (Dχ j) ⊆ W := (tsupport_fderiv_apply_subset ℝ _).trans hs
  let b (i j : Fin d) (x : E) := a x i j * Dχ j x
  have hb (i j : Fin d) : ContDiff ℝ ∞ (b i j) := (ha i j).mul (hDχ j)
  have hbc (i j : Fin d) : HasCompactSupport (b i j) := (hDχc j).mul_left
  have hbs (i j : Fin d) : tsupport (b i j) ⊆ W := tsupport_mul_subset_right.trans (hDχs j)
  let Db (i j : Fin d) (x : E) := fderiv ℝ (b i j) x (EuclideanSpace.single i 1)
  have hDb (i j : Fin d) : ContDiff ℝ ∞ (Db i j) :=
    ((hb i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hDbc (i j : Fin d) : HasCompactSupport (Db i j) := (hbc i j).fderiv_apply ℝ _
  have hDbs (i j : Fin d) : tsupport (Db i j) ⊆ W :=
    (tsupport_fderiv_apply_subset ℝ _).trans (hbs i j)
  let S (i j : Fin d) (x : E) := Db i j x * u x + b i j x * p i x
  let T (i j : Fin d) (x : E) := a x i j * p j x * Dχ i x
  have hS (i j : Fin d) : MemWkp k 2 (S i j) O :=
    MemWkp.add (by norm_num) hO
      (memWkp_mul_smooth_of_tsupport_subset k hO hW hu.le_succ (hDb i j) (hDbc i j) (hDbs i j))
      (memWkp_mul_smooth_of_tsupport_subset k hO hW (hp i) (hb i j) (hbc i j) (hbs i j))
  have hT (i j : Fin d) : MemWkp k 2 (T i j) O := by
    have hm := memWkp_mul_smooth_of_tsupport_subset k hO hW (hp j)
      ((ha i j).mul (hDχ i)) (hDχc i).mul_left (tsupport_mul_subset_right.trans (hDχs i))
    convert hm using 1
    funext x
    dsimp only [T]
    ring
  have hST (i j : Fin d) := MemWkp.add (by norm_num : (1 : ℝ≥0∞) ≤ 2) hO (hS i j) (hT i j)
  have hsum : MemWkp k 2 (fun x => ∑ i, ∑ j, (S i j x + T i j x)) O :=
    memWkp_sum hO k _ (fun i _ => memWkp_sum hO k _ (fun j _ => hST i j))
  have hχf := memWkp_mul_smooth_of_tsupport_subset k hO hW hf hχ hc hs
  refine ⟨MemWkp.sub (by norm_num) hO hχf hsum, ?_⟩
  intro φ hφ hφc hφs
  let Dφ (i : Fin d) (x : E) := fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hφLp : MemLp φ 2 (volume.restrict O) :=
    (hφ.continuous.memLp_of_hasCompactSupport hφc).restrict O
  have hDφLp (i : Fin d) : MemLp (Dφ i) 2 (volume.restrict O) :=
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hφc.fderiv_apply ℝ _)).restrict O
  let c (i j : Fin d) (x : E) := a x i j * χ x
  have hcLp (i j : Fin d) : MemLp (fun x => c i j x * p j x) 2 (volume.restrict O) :=
    memWkp_mul_smooth_of_tsupport_subset 0 hO hW (hp j).memLp
      ((ha i j).mul hχ) hc.mul_left (tsupport_mul_subset_right.trans hs)
  have hbu (i j : Fin d) : MemLp (fun x => b i j x * u x) 2 (volume.restrict O) :=
    memWkp_mul_smooth_of_tsupport_subset 0 hO hW hu.memLp (hb i j) (hbc i j) (hbs i j)
  have hIBP (i j : Fin d) : (∫ x in O, b i j x * u x * Dφ i x) =
      -(∫ x in O, S i j x * φ x) := by
    have ht := hasWeakPartialDeriv_mul_smooth_of_tsupport_subset hW i hu.memLp
      (hp i).memLp (hw i) (hb i j) (hbc i j) (hbs i j) φ hφ hφc hφs
    convert ht using 1
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only [S, Db]; ring
  have hχzero (x : E) (hx : x ∉ W) : χ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht))
  have hDχzero (i : Fin d) (x : E) (hx : x ∉ W) : Dχ i x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hx (hDχs i ht))
  have hmain := heq (fun x => χ x * φ x) (hχ.mul hφ) hc.mul_right
    (fun x hx => ⟨hs (tsupport_mul_subset_left hx), hφs (tsupport_mul_subset_right hx)⟩)
  have hmainL : (∫ x in W ∩ O, ∑ i, ∑ j, a x i j * p j x *
      fderiv ℝ (fun y => χ y * φ y) x (EuclideanSpace.single i 1)) =
      ∫ x in O, ∑ i, ∑ j, (c i j x * p j x * Dφ i x + T i j x * φ x) := by
    calc
      _ = ∫ x in W ∩ O, ∑ i, ∑ j, (c i j x * p j x * Dφ i x + T i j x * φ x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by
            rw [fderiv_fun_mul (hχ.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
            simp only [add_apply, smul_apply, smul_eq_mul]
            dsimp only [c, T, Dχ, Dφ]
            ring
      _ = _ := integral_inter_eq hW fun x hx => by simp [c, T, hχzero x hx, hDχzero _ x hx]
  have hmainR : (∫ x in W ∩ O, f x * (χ x * φ x)) = ∫ x in O, χ x * f x * φ x := by
    calc
      _ = ∫ x in W ∩ O, χ x * f x * φ x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = _ := integral_inter_eq hW fun x hx => by simp [hχzero x hx]
  change (∫ x in W ∩ O, ∑ i, ∑ j, a x i j * p j x *
    fderiv ℝ (fun y => χ y * φ y) x (EuclideanSpace.single i 1)) = _ at hmain
  rw [hmainL, hmainR] at hmain
  have hsplitMain : (∫ x in O, ∑ i, ∑ j, (c i j x * p j x * Dφ i x + T i j x * φ x)) =
      (∑ i, ∑ j, ∫ x in O, c i j x * p j x * Dφ i x) +
        ∑ i, ∑ j, ∫ x in O, T i j x * φ x := by
    rw [integral_sum_sum (v := fun i j x => c i j x * p j x * Dφ i x + T i j x * φ x)
      (fun i j => ((hcLp i j).integrable_mul (hDφLp i)).add
      ((hT i j).memLp.integrable_mul hφLp))]
    have hadd (i j : Fin d) :
        (∫ x in O, c i j x * p j x * Dφ i x + T i j x * φ x) =
        (∫ x in O, c i j x * p j x * Dφ i x) + ∫ x in O, T i j x * φ x := by
      simpa only [Pi.mul_apply] using integral_add ((hcLp i j).integrable_mul (hDφLp i))
        ((hT i j).memLp.integrable_mul hφLp)
    simp_rw [hadd, Finset.sum_add_distrib]
  rw [hsplitMain] at hmain
  have hχu := memWkp_mul_smooth_of_tsupport_subset (k + 1) hO hW hu hχ hc hs
  have hchosen (j : Fin d) : chosenWeakPartial' 2 j (fun x => χ x * u x) O =ᵐ[volume.restrict O]
      fun x => χ x * p j x + Dχ j x * u x := by
    have hpχ := memWkp_mul_smooth_of_tsupport_subset 0 hO hW (hp j).memLp hχ hc hs
    have huDχ := memWkp_mul_smooth_of_tsupport_subset 0 hO hW hu.memLp
      (hDχ j) (hDχc j) (hDχs j)
    exact HasWeakPartialDeriv.ae_eq hO
      (chosenWeakPartial'_isWeakPartial_of_mem hχu.memW1p j)
      (hasWeakPartialDeriv_mul_smooth_of_tsupport_subset hW j hu.memLp (hp j).memLp (hw j) hχ hc hs)
      ((chosenWeakPartial'_memLp_of_mem hχu.memW1p j).locallyIntegrable (by norm_num))
      ((hpχ.memLp.add huDχ.memLp).locallyIntegrable (by norm_num))
  have hnew : (∫ x in O, ∑ i, ∑ j, a x i j *
      chosenWeakPartial' 2 j (fun y => χ y * u y) O x * Dφ i x) =
      (∑ i, ∑ j, ∫ x in O, c i j x * p j x * Dφ i x) -
        ∑ i, ∑ j, ∫ x in O, S i j x * φ x := by
    calc
      _ = ∫ x in O, ∑ i, ∑ j, (c i j x * p j x * Dφ i x + b i j x * u x * Dφ i x) := by
        apply integral_congr_ae
        filter_upwards [eventually_all.mpr hchosen] with x hx
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hx j]
        dsimp only [c, b]
        ring
      _ = ∑ i, ∑ j, ((∫ x in O, c i j x * p j x * Dφ i x) +
          ∫ x in O, b i j x * u x * Dφ i x) := by
        rw [integral_sum_sum (v := fun i j x => c i j x * p j x * Dφ i x + b i j x * u x * Dφ i x)
          (fun i j => ((hcLp i j).integrable_mul (hDφLp i)).add
          ((hbu i j).integrable_mul (hDφLp i)))]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact integral_add ((hcLp i j).integrable_mul (hDφLp i)) ((hbu i j).integrable_mul (hDφLp i))
      _ = _ := by simp_rw [hIBP, Finset.sum_add_distrib, Finset.sum_neg_distrib]; ring
  have hsource : (∫ x in O, (χ x * f x - ∑ i, ∑ j, (S i j x + T i j x)) * φ x) =
      (∫ x in O, χ x * f x * φ x) -
        ((∑ i, ∑ j, ∫ x in O, S i j x * φ x) + ∑ i, ∑ j, ∫ x in O, T i j x * φ x) := by
    simp_rw [sub_mul]
    have ht := integral_sub (hχf.memLp.integrable_mul hφLp) (hsum.memLp.integrable_mul hφLp)
    simp only [Pi.mul_apply] at ht
    rw [ht]
    congr 1
    simp_rw [Finset.sum_mul, add_mul]
    rw [integral_sum_sum (v := fun i j x => S i j x * φ x + T i j x * φ x)
      (fun i j => ((hS i j).memLp.integrable_mul hφLp).add
      ((hT i j).memLp.integrable_mul hφLp))]
    have hadd (i j : Fin d) : (∫ x in O, S i j x * φ x + T i j x * φ x) =
        (∫ x in O, S i j x * φ x) + ∫ x in O, T i j x * φ x := by
      simpa only [Pi.mul_apply] using integral_add ((hS i j).memLp.integrable_mul hφLp)
        ((hT i j).memLp.integrable_mul hφLp)
    simp_rw [hadd, Finset.sum_add_distrib]
  change (∫ x in O, ∑ i, ∑ j, a x i j *
    chosenWeakPartial' 2 j (fun y => χ y * u y) O x * Dφ i x) =
    ∫ x in O, (χ x * f x - ∑ i, ∑ j, (S i j x + T i j x)) * φ x
  rw [hnew, hsource]
  linarith

end Poincare.Analysis.Sobolev.BoundaryLocalization
