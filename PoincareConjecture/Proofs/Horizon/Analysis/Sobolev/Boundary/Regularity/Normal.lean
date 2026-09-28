import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.NormalDerivative
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.DifferentiatedEquation
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Localization.Sobolev

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped ContDiff ENNReal

namespace Poincare.Analysis.Sobolev.BoundaryNormal

open Weak NirenbergEuclidean Poincare.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
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

theorem exists_weak_divergence_chosenWeakPartial_sobolev
    (k : ℕ) (B : SmoothEllipticBilinearForm d univ)
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    {u f : E → ℝ} (hu : MemWkp (k + 2) 2 u O) (hf : MemWkp (k + 1) 2 f O)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u O x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x)
    (ell : Fin d) :
    ∃ F : E → ℝ, MemWkp k 2 F O ∧
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
        (∫ x in O, ∑ i, ∑ j, B.a x i j *
          chosenWeakPartial' 2 j (chosenWeakPartial' 2 ell u O) O x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, F x * φ x := by
  let p (j : Fin d) := chosenWeakPartial' 2 j u O
  let q (i j : Fin d) := chosenWeakPartial' 2 j (p i) O
  have hp (j : Fin d) : MemWkp (k + 1) 2 (p j) O := hu.chosenWeakPartial_mem j
  have hq (i j : Fin d) : MemWkp k 2 (q i j) O := (hp i).chosenWeakPartial_mem j
  have hw (i j : Fin d) : HasWeakPartialDeriv i (q i j) (p j) O :=
    BoundaryTangential.weakPartial_commute i j
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i)
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p j)
      (chosenWeakPartial'_isWeakPartial_of_mem (hp i).memW1p j)
  let da (i j : Fin d) (x : E) :=
    fderiv ℝ (fun y => B.a y i j) x (EuclideanSpace.single ell 1)
  have hda (i j : Fin d) : ContDiff ℝ ∞ (da i j) :=
    ((B.smooth_a i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  let G (i j : Fin d) (x : E) :=
    fderiv ℝ (da i j) x (EuclideanSpace.single i 1) * p j x + da i j x * q i j x
  have hG (i j : Fin d) : MemWkp k 2 (G i j) O :=
    MemWkp.add (by norm_num) hO
      (BoundaryLocalization.memWkp_mul_smooth_of_isCompact_closure k hO hOc (hp j).le_succ
        (((hda i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const))
      (BoundaryLocalization.memWkp_mul_smooth_of_isCompact_closure k hO hOc (hq i j) (hda i j))
  let F : E → ℝ := fun x => chosenWeakPartial' 2 ell f O x + ∑ i, ∑ j, G i j x
  have hF : MemWkp k 2 F O :=
    MemWkp.add (by norm_num) hO (hf.chosenWeakPartial_mem ell)
      (memWkp_sum hO k _ (fun i _ => memWkp_sum hO k _ (fun j _ => hG i j)))
  refine ⟨F, hF, ?_⟩
  exact (BoundaryTangential.differentiated_weak_divergence hO hOc B.a B.smooth_a ell
    (fun j => (hp j).memLp) (fun i j => (hq i j).memLp) hw hf.memLp
    (hf.chosenWeakPartial_mem ell).memLp
    (chosenWeakPartial'_isWeakPartial_of_mem hf.memW1p ell) heq).2

theorem memWkp_add_two_of_tangential_memWkp_succ
    (k : ℕ) (B : SmoothEllipticBilinearForm d univ)
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    {u f : E → ℝ} (hu : MemWkp (k + 1) 2 u O) (hf : MemWkp k 2 f O)
    (htan : ∀ i : Fin d, i ≠ 0 → MemWkp (k + 1) 2 (chosenWeakPartial' 2 i u O) O)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u O x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) :
    MemWkp (k + 2) 2 u O := by
  induction k generalizing u f with
  | zero =>
    apply memWkp_two_of_tangential_weakDerivatives B hO hOc hu.memLp hf.memLp
      (fun i => chosenWeakPartial'_memLp_of_mem hu.memW1p i)
      (fun i => chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i)
      (heq := heq)
    intro i hi j
    refine ⟨chosenWeakPartial' 2 j (chosenWeakPartial' 2 i u O) O,
      chosenWeakPartial'_memLp_of_mem (htan i hi).memW1p j, ?_⟩
    exact BoundaryTangential.weakPartial_commute i j
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i)
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p j)
      (chosenWeakPartial'_isWeakPartial_of_mem (htan i hi).memW1p j)
  | succ k ih =>
    let p (i : Fin d) := chosenWeakPartial' 2 i u O
    have hp (i : Fin d) : MemWkp (k + 1) 2 (p i) O := hu.chosenWeakPartial_mem i
    obtain ⟨F, hF, hFeq⟩ :=
      exists_weak_divergence_chosenWeakPartial_sobolev k B hO hOc hu hf heq 0
    have hptan (i : Fin d) (hi : i ≠ 0) :
        MemWkp (k + 1) 2 (chosenWeakPartial' 2 i (p 0) O) O := by
      let v := chosenWeakPartial' 2 0 (p i) O
      have hv : MemWkp (k + 1) 2 v O := (htan i hi).chosenWeakPartial_mem 0
      have hwv : HasWeakPartialDeriv i v (p 0) O :=
        BoundaryTangential.weakPartial_commute i 0
          (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i)
          (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p 0)
          (chosenWeakPartial'_isWeakPartial_of_mem (htan i hi).memW1p 0)
      have hae : chosenWeakPartial' 2 i (p 0) O =ᵐ[volume.restrict O] v :=
        HasWeakPartialDeriv.ae_eq hO
          (chosenWeakPartial'_isWeakPartial_of_mem (hp 0).memW1p i) hwv
          ((chosenWeakPartial'_memLp_of_mem (hp 0).memW1p i).locallyIntegrable (by norm_num))
          (hv.memLp.locallyIntegrable (by norm_num))
      exact (MemWkp_congr_ae (by norm_num) hO hae).mpr hv
    have hp0 : MemWkp (k + 2) 2 (p 0) O := ih (hp 0) hF hptan hFeq
    refine ⟨hu.memW1p, fun i => ?_⟩
    by_cases hi : i = 0
    · simpa only [hi] using hp0
    · exact htan i hi

end Poincare.Analysis.Sobolev.BoundaryNormal
