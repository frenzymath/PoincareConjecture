import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Approximation.TangentialDerivative
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.LocalTangentialRegularity
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.NormalH3
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.LocalEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff ENNReal

namespace Poincare.Analysis.Sobolev.BoundaryTangential

open Weak NirenbergEuclidean Poincare.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem principal_restrict {O V : Set E} (hs : V ⊆ O)
    {a : E → Matrix (Fin d) (Fin d) ℝ} {p : Fin d → E → ℝ} {f : E → ℝ}
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, a x i j * p j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ x in V, ∑ i, ∑ j, a x i j * p j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in V, f x * φ x := by
  intro φ hφ hc ht
  simpa only [Finset.sum_mul] using
    Poincare.Analysis.Elliptic.weakEquation_congr_restrict hs
      (a := a) (q := p) (fun _ _ => rfl) (fun _ _ _ => rfl) heq φ hφ hc ht

omit [NeZero d] in
private theorem memLp_coeff_mul {W O : Set E} (hWc : IsCompact (closure W))
    (hO : IsOpen O) (hs : O ⊆ W) {a v : E → ℝ} (ha : Continuous a)
    (hv : MemLp v 2 (volume.restrict O)) :
    MemLp (fun x => a x * v x) 2 (volume.restrict O) := by
  obtain ⟨C, hC⟩ := hWc.exists_bound_of_continuousOn ha.continuousOn
  apply hv.of_le_mul (c := C) (ha.aestronglyMeasurable.mul hv.1)
  filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x (subset_closure (hs hx))) (norm_nonneg _)

omit [NeZero d] in
private theorem memLp_compact_mul {O : Set E} {a v : E → ℝ}
    (ha : Continuous a) (hc : HasCompactSupport a)
    (hv : MemLp v 2 (volume.restrict O)) :
    MemLp (fun x => a x * v x) 2 (volume.restrict O) := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous ha
  apply hv.of_le_mul (c := C) (ha.aestronglyMeasurable.mul hv.1)
  exact Eventually.of_forall fun x => by
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

private theorem memWkp_two_of_local_principal
    (B : SmoothEllipticBilinearForm d univ)
    {W V : Set E} (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {u f : E → ℝ} {p : Fin d → E → ℝ}
    (hu : MemW01p 2 u (halfSpace d))
    (hf : MemLp f 2 (volume.restrict (W ∩ halfSpace d)))
    (hp : ∀ i, MemLp (p i) 2 (volume.restrict (halfSpace d)))
    (hw : ∀ i, HasWeakPartialDeriv i (p i) u (halfSpace d))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ W ∩ halfSpace d →
      (∫ x in W ∩ halfSpace d, ∑ i, ∑ j, B.a x i j * p j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in W ∩ halfSpace d, f x * φ x) :
    MemWkp 2 2 u (V ∩ halfSpace d) := by
  have hWH := hW.inter isOpen_halfSpace
  have hVH := hV.inter isOpen_halfSpace
  have hsub : V ∩ halfSpace d ⊆ W ∩ halfSpace d :=
    inter_subset_inter_left _ (subset_closure.trans hVW)
  have hF (j : Fin d) : MemLp (fun x => ∑ i : Fin d, B.a x i j * p i x)
      2 (volume.restrict (W ∩ halfSpace d)) :=
    memLp_finsetSum _ (fun i _ => memLp_coeff_mul hWc hWH inter_subset_left
      (B.smooth_a i j).continuous
      ((hp i).mono_measure (Measure.restrict_mono_set volume inter_subset_right)))
  have heq' : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ W ∩ halfSpace d →
      (∫ x in W ∩ halfSpace d, ∑ j : Fin d,
        (∑ i : Fin d, B.a x i j * p i x) *
          fderiv ℝ φ x (EuclideanSpace.single j 1)) =
        ∫ x in W ∩ halfSpace d, f x * φ x := by
    intro φ hφ hc hs
    rw [← heq φ hφ hc hs]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [B.symm x j i]
  apply BoundaryNormal.memWkp_two_of_tangential_weakDerivatives B hVH
    (hVc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left))
    (hu.1.1.mono_measure (Measure.restrict_mono_set volume inter_subset_right))
    (hf.mono_measure (Measure.restrict_mono_set volume hsub))
    (fun i => (hp i).mono_measure (Measure.restrict_mono_set volume inter_subset_right))
    (fun i => (hw i).restrict hVH inter_subset_right)
    (exists_tangential_weakPartial_of_local_weakEquation B hW hV hVc hVW hu hf hp hw hF heq')
  exact principal_restrict hsub heq

theorem memWkp_three_of_weakEquation
    (B : SmoothEllipticBilinearForm d univ)
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    {u f : E → ℝ} (hu0 : MemW01p 2 u (halfSpace d))
    (hu2 : MemWkp 2 2 u (halfSpace d)) (hf : MemW1p 2 f (halfSpace d))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfSpace d →
      (∫ x in halfSpace d, ∑ i, ∑ j,
        B.a x i j * chosenWeakPartial' 2 j u (halfSpace d) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in halfSpace d, f x * φ x) :
    MemWkp 3 2 u (V ∩ halfSpace d) := by
  classical
  let H := halfSpace d
  let p (i : Fin d) := chosenWeakPartial' 2 i u H
  let q (i j : Fin d) := chosenWeakPartial' 2 j (p i) H
  have hp (i : Fin d) : MemW1p 2 (p i) H := (hu2.chosenWeakPartial_mem i).memW1p
  have hw (i : Fin d) : HasWeakPartialDeriv i (p i) u H :=
    chosenWeakPartial'_isWeakPartial_of_mem hu2.memW1p i
  have hq (i j : Fin d) : MemLp (q i j) 2 (volume.restrict H) :=
    chosenWeakPartial'_memLp_of_mem (hp i) j
  have hwq (i j : Fin d) : HasWeakPartialDeriv j (q i j) (p i) H :=
    chosenWeakPartial'_isWeakPartial_of_mem (hp i) j
  obtain ⟨W, hW, hVW, hWc⟩ := exists_isOpen_superset_and_isCompact_closure hVc
  obtain ⟨U, hU, hWU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hWc
  have hWsub : W ⊆ U := subset_closure.trans hWU
  have hUH : IsOpen (U ∩ H) := hU.inter isOpen_halfSpace
  have hWH : IsOpen (W ∩ H) := hW.inter isOpen_halfSpace
  have hVH : IsOpen (V ∩ H) := hV.inter isOpen_halfSpace
  have hUHc : IsCompact (closure (U ∩ H)) :=
    hUc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  have hVHc : IsCompact (closure (V ∩ H)) :=
    hVc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  obtain ⟨χ, hχ, hχc, _, hχone, _⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff hWc hU hWU
  have huV : MemWkp 2 2 u (V ∩ H) :=
    hu2.mono_set (by norm_num) hVH inter_subset_right
  have hfV : MemW1p 2 f (V ∩ H) :=
    MemW1p.mono_set hVH inter_subset_right hf
  have hpV (i : Fin d) : p i =ᵐ[volume.restrict (V ∩ H)]
      chosenWeakPartial' 2 i u (V ∩ H) :=
    chosenWeakPartial'_mono_set_ae (by norm_num) hVH inter_subset_right hu2.memW1p i
  have heqV : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ V ∩ H →
      (∫ x in V ∩ H, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j u (V ∩ H) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in V ∩ H, f x * φ x := by
    intro φ hφ hc hs
    rw [← principal_restrict inter_subset_right heq φ hφ hc hs]
    apply integral_congr_ae
    filter_upwards [eventually_all.mpr hpV] with x hx
    simp only [← hx, p, H]
  apply BoundaryNormal.memWkp_three_of_tangential_memWkp_two B hVH hVHc huV hfV
    (heq := heqV)
  intro k hk
  obtain ⟨F, hF, hFeq⟩ : ∃ F : E → ℝ, MemLp F 2 (volume.restrict (U ∩ H)) ∧
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U ∩ H →
        (∫ x in U ∩ H, ∑ i, ∑ j, B.a x i j * q k j x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in U ∩ H, F x * φ x := by
    refine ⟨_, differentiated_weak_divergence hUH hUHc B.a B.smooth_a k
      (fun j => (hp j).1.mono_measure (Measure.restrict_mono_set volume inter_subset_right))
      (fun i j => (hq i j).mono_measure (Measure.restrict_mono_set volume inter_subset_right))
      (fun i j => (weakPartial_commute i j (hw i) (hw j) (hwq i j)).restrict hUH inter_subset_right)
      (hf.1.mono_measure (Measure.restrict_mono_set volume inter_subset_right))
      ((chosenWeakPartial'_memLp_of_mem hf k).mono_measure
        (Measure.restrict_mono_set volume inter_subset_right))
      ((chosenWeakPartial'_isWeakPartial_of_mem hf k).restrict hUH inter_subset_right)
      (principal_restrict inter_subset_right heq)⟩
  let v : E → ℝ := fun x => χ x * p k x
  let r (j : Fin d) (x : E) :=
    χ x * q k j x + fderiv ℝ χ x (EuclideanSpace.single j 1) * p k x
  have hv0 : MemW01p 2 v H :=
    memW01p_mul_chosenWeakPartial_tangential hu0 hu2 hχ hχc k hk
  have hr (j : Fin d) : MemLp (r j) 2 (volume.restrict H) :=
    (memLp_compact_mul hχ.continuous hχc (hq k j)).add
      (memLp_compact_mul ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
        (hχc.fderiv_apply ℝ _) (hp k).1)
  have hwr (j : Fin d) : HasWeakPartialDeriv j (r j) v H :=
    (hwq k j).mul_smooth isOpen_halfSpace hχ
      ((hp k).1.locallyIntegrable (by norm_num)) ((hq k j).locallyIntegrable (by norm_num))
  have hvr := Poincare.Analysis.Elliptic.cutoff_eqOn_of_eq_one
    (u := p k) (p := q k) hW (fun x hx => hχone x (subset_closure hx))
  have hFeqW : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ W ∩ H →
      (∫ x in W ∩ H, ∑ i, ∑ j, B.a x i j * r j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in W ∩ H, F x * φ x := by
    intro φ hφ hc hs
    simpa only [Finset.sum_mul] using Poincare.Analysis.Elliptic.weakEquation_congr_restrict
      (inter_subset_inter_left H hWsub) (a := B.a) (q := r)
      (fun _ _ => rfl) (fun j x hx => hvr.2 j hx.1) hFeq φ hφ hc hs
  have hv2 : MemWkp 2 2 v (V ∩ H) :=
    memWkp_two_of_local_principal B hW hWc hV hVc hVW hv0
      (hF.mono_measure (Measure.restrict_mono_set volume (inter_subset_inter_left H hWsub)))
      hr hwr hFeqW
  apply (MemWkp_congr_ae (by norm_num) hVH (v := chosenWeakPartial' 2 k u (V ∩ H)) ?_).mp hv2
  filter_upwards [hpV k, ae_restrict_mem hVH.measurableSet] with x hx hxV
  change χ x * p k x = _
  rw [hχone x (subset_closure (hVW (subset_closure hxV.1))), one_mul, hx]

end Poincare.Analysis.Sobolev.BoundaryTangential
