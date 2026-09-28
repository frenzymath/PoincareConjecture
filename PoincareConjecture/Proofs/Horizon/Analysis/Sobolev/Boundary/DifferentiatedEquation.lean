import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Iterated.Basic








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff

namespace Poincare.Analysis.Sobolev.BoundaryTangential

open Weak

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

private theorem memLp_coeff_mul {O : Set E} (hO : IsOpen O)
    (hOc : IsCompact (closure O)) {a v : E → ℝ} (ha : Continuous a)
    (hv : MemLp v 2 (volume.restrict O)) :
    MemLp (fun x => a x * v x) 2 (volume.restrict O) := by
  obtain ⟨C, hC⟩ := hOc.exists_bound_of_continuousOn ha.continuousOn
  apply hv.of_le_mul (c := C) (ha.aestronglyMeasurable.mul hv.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x (subset_closure hx)) (norm_nonneg _)



theorem differentiated_weak_divergence
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {p : Fin d → E → ℝ} {q : Fin d → Fin d → E → ℝ}
    {f r : E → ℝ} (k : Fin d)
    (hp : ∀ j, MemLp (p j) 2 (volume.restrict O))
    (hq : ∀ i j, MemLp (q i j) 2 (volume.restrict O))
    (hw : ∀ i j, HasWeakPartialDeriv i (q i j) (p j) O)
    (_hf : MemLp f 2 (volume.restrict O))
    (hr : MemLp r 2 (volume.restrict O))
    (hfr : HasWeakPartialDeriv k r f O)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, a x i j * p j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) :
    let F : E → ℝ := fun x => r x + ∑ i, ∑ j,
      (fderiv ℝ (fun y => fderiv ℝ (fun z => a z i j) y
        (EuclideanSpace.single k 1)) x (EuclideanSpace.single i 1) * p j x +
      fderiv ℝ (fun y => a y i j) x (EuclideanSpace.single k 1) * q i j x)
    MemLp F 2 (volume.restrict O) ∧
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
        (∫ x in O, ∑ i, ∑ j, a x i j * q k j x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, F x * φ x := by
  classical
  let da (i j : Fin d) (x : E) :=
    fderiv ℝ (fun y => a y i j) x (EuclideanSpace.single k 1)
  have hda (i j : Fin d) : ContDiff ℝ ∞ (da i j) :=
    ((ha i j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  let G (i j : Fin d) (x : E) :=
    fderiv ℝ (da i j) x (EuclideanSpace.single i 1) * p j x + da i j x * q i j x
  have hG (i j : Fin d) : MemLp (G i j) 2 (volume.restrict O) :=
    (memLp_coeff_mul hO hOc
      (((hda i j).continuous_fderiv (by simp)).clm_apply continuous_const) (hp j)).add
      (memLp_coeff_mul hO hOc (hda i j).continuous (hq i j))
  have hsumG : MemLp (fun x => ∑ i, ∑ j, G i j x) 2 (volume.restrict O) :=
    memLp_finsetSum _ (fun i _ => memLp_finsetSum _ (fun j _ => hG i j))
  refine ⟨hr.add hsumG, ?_⟩
  intro φ hφ hc hs
  let D (i : Fin d) (x : E) := fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hD (i : Fin d) : ContDiff ℝ ∞ (D i) :=
    (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hDc (i : Fin d) : HasCompactSupport (D i) := hc.fderiv_apply ℝ _
  have hDs (i : Fin d) : tsupport (D i) ⊆ O := (tsupport_fderiv_apply_subset ℝ _).trans hs
  have hφLp : MemLp φ 2 (volume.restrict O) :=
    (hφ.continuous.memLp_of_hasCompactSupport hc).restrict O
  have hDLp (i : Fin d) : MemLp (D i) 2 (volume.restrict O) :=
    ((hD i).continuous.memLp_of_hasCompactSupport (hDc i)).restrict O
  have hDDLp (i j : Fin d) : MemLp
      (fun x => fderiv ℝ (D i) x (EuclideanSpace.single j 1)) 2 (volume.restrict O) :=
    ((((hD i).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hDc i).fderiv_apply ℝ _)).restrict O
  have hap (i j : Fin d) : MemLp (fun x => a x i j * p j x) 2 (volume.restrict O) :=
    memLp_coeff_mul hO hOc (ha i j).continuous (hp j)
  have haq (i j : Fin d) : MemLp (fun x => a x i j * q k j x) 2 (volume.restrict O) :=
    memLp_coeff_mul hO hOc (ha i j).continuous (hq k j)
  have hdap (i j : Fin d) : MemLp (fun x => da i j x * p j x) 2 (volume.restrict O) :=
    memLp_coeff_mul hO hOc (hda i j).continuous (hp j)
  have hterm (i j : Fin d) :
      (∫ x in O, a x i j * p j x * fderiv ℝ (D k) x (EuclideanSpace.single i 1)) =
        -(∫ x in O, a x i j * q k j x * D i x) + ∫ x in O, G i j x * φ x := by
    have h1 := (hw k j).mul_smooth hO (ha i j)
      ((hp j).locallyIntegrable (by norm_num)) ((hq k j).locallyIntegrable (by norm_num))
      (D i) (hD i) (hDc i) (hDs i)
    have h2 := (hw i j).mul_smooth hO (hda i j)
      ((hp j).locallyIntegrable (by norm_num)) ((hq i j).locallyIntegrable (by norm_num))
      φ hφ hc hs
    have hcomm : (∫ x in O, a x i j * p j x *
        fderiv ℝ (D k) x (EuclideanSpace.single i 1)) =
        ∫ x in O, a x i j * p j x * fderiv ℝ (D i) x (EuclideanSpace.single k 1) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => congrArg (a x i j * p j x * ·)
        (partial_test_symmetric hφ k i x)
    have hsplit : (∫ x in O, (a x i j * q k j x + da i j x * p j x) * D i x) =
        (∫ x in O, a x i j * q k j x * D i x) +
        ∫ x in O, da i j x * p j x * D i x := by
      simp_rw [add_mul]
      exact integral_add ((haq i j).integrable_mul (hDLp i))
        ((hdap i j).integrable_mul (hDLp i))
    have hGswap : (∫ x in O, (da i j x * q i j x +
        fderiv ℝ (da i j) x (EuclideanSpace.single i 1) * p j x) * φ x) =
        ∫ x in O, G i j x * φ x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [G]; ring
    change (∫ x in O, a x i j * p j x *
      fderiv ℝ (D i) x (EuclideanSpace.single k 1)) =
      -(∫ x in O, (a x i j * q k j x + da i j x * p j x) * D i x) at h1
    change (∫ x in O, da i j x * p j x * D i x) =
      -(∫ x in O, (da i j x * q i j x +
        fderiv ℝ (da i j) x (EuclideanSpace.single i 1) * p j x) * φ x) at h2
    rw [hsplit] at h1
    rw [hGswap] at h2
    linarith
  have hmain := heq (D k) (hD k) (hDc k) (hDs k)
  have horig : (∫ x in O, ∑ i, ∑ j, a x i j * p j x *
      fderiv ℝ (D k) x (EuclideanSpace.single i 1)) =
      ∑ i, ∑ j, ∫ x in O, a x i j * p j x *
        fderiv ℝ (D k) x (EuclideanSpace.single i 1) := by
    have hsum := integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => (hap i j).integrable_mul (hDDLp k i)))
    simp only [Pi.mul_apply] at hsum
    rw [hsum]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _
      (fun j _ => (hap i j).integrable_mul (hDDLp k i))
  have hnew : (∫ x in O, ∑ i, ∑ j, a x i j * q k j x * D i x) =
      ∑ i, ∑ j, ∫ x in O, a x i j * q k j x * D i x := by
    have hsum := integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => (haq i j).integrable_mul (hDLp i)))
    simp only [Pi.mul_apply] at hsum
    rw [hsum]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _
      (fun j _ => (haq i j).integrable_mul (hDLp i))
  have hsource : (∫ x in O, (r x + ∑ i, ∑ j, G i j x) * φ x) =
      (∫ x in O, r x * φ x) + ∑ i, ∑ j, ∫ x in O, G i j x * φ x := by
    simp_rw [add_mul]
    have hadd := integral_add (hr.integrable_mul hφLp) (hsumG.integrable_mul hφLp)
    simp only [Pi.mul_apply] at hadd
    rw [hadd]
    simp_rw [Finset.sum_mul]
    have hsum := integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
      (fun j _ => (hG i j).integrable_mul hφLp))
    simp only [Pi.mul_apply] at hsum
    rw [hsum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _
      (fun j _ => (hG i j).integrable_mul hφLp)
  rw [horig] at hmain
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_neg_distrib] at hmain
  have hright := hfr φ hφ hc hs
  change (∫ x in O, f x * D k x) = -(∫ x in O, r x * φ x) at hright
  change (∫ x in O, ∑ i, ∑ j, a x i j * q k j x * D i x) =
    ∫ x in O, (r x + ∑ i, ∑ j, G i j x) * φ x
  rw [hnew, hsource]
  linarith


theorem weakPartial_commute {O : Set E} {u pi pj q : E → ℝ}
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

open Poincare.Analysis.Sobolev.Euclidean



theorem exists_weak_divergence_chosenWeakPartial
    {O : Set E} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (a : E → Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {u f : E → ℝ} (hu : MemWkp 2 2 u O) (hf : MemW1p 2 f O)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, a x i j * chosenWeakPartial' 2 j u O x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x)
    (k : Fin d) :
    ∃ F : E → ℝ, MemLp F 2 (volume.restrict O) ∧
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
        (∫ x in O, ∑ i, ∑ j, a x i j *
          chosenWeakPartial' 2 j (chosenWeakPartial' 2 k u O) O x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, F x * φ x := by
  let p (j : Fin d) := chosenWeakPartial' 2 j u O
  let q (i j : Fin d) := chosenWeakPartial' 2 j (p i) O
  have hp (j : Fin d) : MemW1p 2 (p j) O := (hu.chosenWeakPartial_mem j).memW1p
  have hq (i j : Fin d) : MemLp (q i j) 2 (volume.restrict O) :=
    chosenWeakPartial'_memLp_of_mem (hp i) j
  have hw (i j : Fin d) : HasWeakPartialDeriv i (q i j) (p j) O :=
    weakPartial_commute i j
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i)
      (chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p j)
      (chosenWeakPartial'_isWeakPartial_of_mem (hp i) j)
  exact ⟨_, differentiated_weak_divergence hO hOc a ha k
    (fun j => (hp j).1) hq hw hf.1 (chosenWeakPartial'_memLp_of_mem hf k)
    (chosenWeakPartial'_isWeakPartial_of_mem hf k) heq⟩

end Poincare.Analysis.Sobolev.BoundaryTangential
