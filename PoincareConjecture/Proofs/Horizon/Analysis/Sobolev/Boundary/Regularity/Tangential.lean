import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Regularity.Normal
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Approximation.TangentialDerivative
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.LocalTangentialRegularity
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Localization.WeakEquation
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
private theorem chosen_equation_restrict {O V : Set E} (hV : IsOpen V) (hs : V ⊆ O)
    {a : E → Matrix (Fin d) (Fin d) ℝ} {u f : E → ℝ} (hu : MemW1p 2 u O)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, a x i j * chosenWeakPartial' 2 j u O x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      (∫ x in V, ∑ i, ∑ j, a x i j * chosenWeakPartial' 2 j u V x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in V, f x * φ x := by
  have hp (j : Fin d) := chosenWeakPartial'_mono_set_ae (by norm_num) hV hs hu j
  intro φ hφ hc ht
  rw [← principal_restrict hs heq φ hφ hc ht]
  apply integral_congr_ae
  filter_upwards [eventually_all.mpr hp] with x hx
  simp only [← hx]

omit [NeZero d] in
private theorem chosen_equation_congr {O : Set E} (hO : IsOpen O)
    {a : E → Matrix (Fin d) (Fin d) ℝ} {u v f : E → ℝ}
    (huv : u =ᵐ[volume.restrict O] v)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, a x i j * chosenWeakPartial' 2 j u O x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x) :
    ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, a x i j * chosenWeakPartial' 2 j v O x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x := by
  have hp (j : Fin d) := chosenWeakPartial'_ae_congr (p := 2) (by norm_num) hO huv j
  intro φ hφ hc ht
  rw [← heq φ hφ hc ht]
  apply integral_congr_ae
  filter_upwards [eventually_all.mpr hp] with x hx
  simp only [← hx]

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

private theorem local_H2
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

private theorem upgrade_global
    (k : ℕ) (B : SmoothEllipticBilinearForm d univ)
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    {u f : E → ℝ} (hu0 : MemW01p 2 u (halfSpace d))
    (hu : MemWkp (k + 1) 2 u (halfSpace d)) (hf : MemWkp k 2 f (halfSpace d))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfSpace d →
      (∫ x in halfSpace d, ∑ i, ∑ j,
        B.a x i j * chosenWeakPartial' 2 j u (halfSpace d) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in halfSpace d, f x * φ x) :
    MemWkp (k + 2) 2 u (V ∩ halfSpace d) := by
  induction k generalizing V u f with
  | zero =>
    obtain ⟨W, hW, hVW, hWc⟩ := exists_isOpen_superset_and_isCompact_closure hVc
    exact local_H2 B hW hWc hV hVc hVW hu0
      (hf.memLp.mono_measure (Measure.restrict_mono_set volume inter_subset_right))
      (fun i => chosenWeakPartial'_memLp_of_mem hu.memW1p i)
      (fun i => chosenWeakPartial'_isWeakPartial_of_mem hu.memW1p i)
      (principal_restrict inter_subset_right heq)
  | succ k ih =>
    let H := halfSpace d
    have hVH : IsOpen (V ∩ H) := hV.inter isOpen_halfSpace
    have hVHc : IsCompact (closure (V ∩ H)) :=
      hVc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
    have huV : MemWkp (k + 2) 2 u (V ∩ H) :=
      hu.mono_set (by norm_num) hVH inter_subset_right
    have hfV : MemWkp (k + 1) 2 f (V ∩ H) :=
      hf.mono_set (by norm_num) hVH inter_subset_right
    have heqV := chosen_equation_restrict hVH inter_subset_right hu.memW1p heq
    apply BoundaryNormal.memWkp_add_two_of_tangential_memWkp_succ (k + 1) B hVH hVHc
      huV hfV (heq := heqV)
    intro ell hell
    obtain ⟨U, hU, hVU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hVc
    have hUH : IsOpen (U ∩ H) := hU.inter isOpen_halfSpace
    have hUHc : IsCompact (closure (U ∩ H)) :=
      hUc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
    have huU : MemWkp (k + 2) 2 u (U ∩ H) :=
      hu.mono_set (by norm_num) hUH inter_subset_right
    have hfU : MemWkp (k + 1) 2 f (U ∩ H) :=
      hf.mono_set (by norm_num) hUH inter_subset_right
    obtain ⟨F, hF, hFeq⟩ :=
      BoundaryNormal.exists_weak_divergence_chosenWeakPartial_sobolev k B hUH hUHc huU hfU
        (chosen_equation_restrict hUH inter_subset_right hu.memW1p heq) ell
    let p := chosenWeakPartial' 2 ell u H
    have hp : MemWkp (k + 1) 2 p H := hu.chosenWeakPartial_mem ell
    have hpU : MemWkp (k + 1) 2 p (U ∩ H) :=
      hp.mono_set (by norm_num) hUH inter_subset_right
    have hpeq : p =ᵐ[volume.restrict (U ∩ H)] chosenWeakPartial' 2 ell u (U ∩ H) :=
      chosenWeakPartial'_mono_set_ae (by norm_num) hUH inter_subset_right hu.memW1p ell
    have hFeqp := chosen_equation_congr hUH hpeq.symm hFeq
    obtain ⟨χ, hχ, hc, _, hone, hs⟩ :=
      SmoothEllipticBilinearForm.exists_cutoff hVc hU hVU
    let v : E → ℝ := fun x => χ x * p x
    have hv0 : MemW01p 2 v H :=
      memW01p_mul_chosenWeakPartial_tangential hu0
        (hu.le_of_le (by omega : 2 ≤ k + 1 + 1)) hχ hc ell hell
    have hv : MemWkp (k + 1) 2 v H :=
      BoundaryLocalization.memWkp_mul_smooth_of_tsupport_subset (k + 1)
        isOpen_halfSpace hU hpU hχ hc hs
    obtain ⟨G, hG, hGeq⟩ : ∃ G : E → ℝ, MemWkp k 2 G H ∧
        ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ H →
          (∫ x in H, ∑ i, ∑ j, B.a x i j * chosenWeakPartial' 2 j v H x *
            fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in H, G x * φ x :=
      ⟨_, BoundaryLocalization.localize_weak_divergence k isOpen_halfSpace hU
        B.a B.smooth_a hpU hF hχ hc hs hFeqp⟩
    have hvreg : MemWkp (k + 2) 2 v (V ∩ H) := ih hV hVc hv0 hv hG hGeq
    apply (MemWkp_congr_ae (by norm_num) hVH
      (v := chosenWeakPartial' 2 ell u (V ∩ H)) ?_).mp hvreg
    have hpV := chosenWeakPartial'_mono_set_ae (by norm_num) hVH inter_subset_right hu.memW1p ell
    filter_upwards [hpV, ae_restrict_mem hVH.measurableSet] with x hx hxV
    change χ x * p x = _
    rw [hone x (subset_closure hxV.1), one_mul]
    exact hx

private theorem upgrade_local
    (k : ℕ) (B : SmoothEllipticBilinearForm d univ)
    {W V : Set E} (hW : IsOpen W) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {u f : E → ℝ} (hu0 : MemW01p 2 u (halfSpace d))
    (hu : MemWkp (k + 1) 2 u (W ∩ halfSpace d))
    (hf : MemWkp k 2 f (W ∩ halfSpace d))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ W ∩ halfSpace d →
      (∫ x in W ∩ halfSpace d, ∑ i, ∑ j,
        B.a x i j * chosenWeakPartial' 2 j u (W ∩ halfSpace d) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in W ∩ halfSpace d, f x * φ x) :
    MemWkp (k + 2) 2 u (V ∩ halfSpace d) := by
  obtain ⟨χ, hχ, hc, _, hone, hs⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff hVc hW hVW
  let v : E → ℝ := fun x => χ x * u x
  have hv0 : MemW01p 2 v (halfSpace d) := memW01p_mul_smooth isOpen_halfSpace hu0 hχ hc
  have hv : MemWkp (k + 1) 2 v (halfSpace d) :=
    BoundaryLocalization.memWkp_mul_smooth_of_tsupport_subset (k + 1)
      isOpen_halfSpace hW hu hχ hc hs
  obtain ⟨F, hF, hFeq⟩ : ∃ F : E → ℝ, MemWkp k 2 F (halfSpace d) ∧
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ halfSpace d →
        (∫ x in halfSpace d, ∑ i, ∑ j, B.a x i j *
          chosenWeakPartial' 2 j v (halfSpace d) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in halfSpace d, F x * φ x :=
    ⟨_, BoundaryLocalization.localize_weak_divergence k isOpen_halfSpace hW
      B.a B.smooth_a hu hf hχ hc hs heq⟩
  have hvreg := upgrade_global k B hV hVc hv0 hv hF hFeq
  apply (MemWkp_congr_ae (by norm_num) (hV.inter isOpen_halfSpace) (v := u) ?_).mp hvreg
  filter_upwards [ae_restrict_mem (hV.inter isOpen_halfSpace).measurableSet] with x hx
  exact congrArg (· * u x) (hone x (subset_closure hx.1)) |>.trans (one_mul _)

omit [NeZero d] in
private theorem exists_precompact_between {W V : Set E}
    (hW : IsOpen W) (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W) :
    ∃ U, IsOpen U ∧ closure V ⊆ U ∧ IsCompact (closure U) ∧ closure U ⊆ W := by
  obtain ⟨U₀, hU₀, hVU₀, hU₀c⟩ := exists_isOpen_superset_and_isCompact_closure hVc
  obtain ⟨U, hU, hVU, hUW⟩ := hVc.exists_isOpen_closure_subset
    ((hW.inter hU₀).mem_nhdsSet.mpr (subset_inter hVW hVU₀))
  refine ⟨U, hU, hVU, ?_, fun x hx => (hUW hx).1⟩
  exact hU₀c.of_isClosed_subset isClosed_closure
    (fun x hx => subset_closure (hUW hx).2)



theorem memWkp_add_two_of_local_weakEquation
    (k : ℕ) (B : SmoothEllipticBilinearForm d univ)
    {W V : Set E} (hW : IsOpen W) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {u f : E → ℝ} (hu0 : MemW01p 2 u (halfSpace d))
    (hf : MemWkp k 2 f (W ∩ halfSpace d))
    (heq : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ W ∩ halfSpace d →
      (∫ x in W ∩ halfSpace d, ∑ i, ∑ j,
        B.a x i j * chosenWeakPartial' 2 j u (W ∩ halfSpace d) x *
          fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in W ∩ halfSpace d, f x * φ x) :
    MemWkp (k + 2) 2 u (V ∩ halfSpace d) := by
  induction k generalizing V with
  | zero =>
    exact upgrade_local 0 B hW hV hVc hVW hu0
      (MemWkp.one_iff_memW1p.mpr (MemW1p.mono_set (hW.inter isOpen_halfSpace)
        inter_subset_right hu0.1)) hf heq
  | succ k ih =>
    obtain ⟨U, hU, hVU, hUc, hUW⟩ := exists_precompact_between hW hVc hVW
    have huU : MemWkp (k + 2) 2 u (U ∩ halfSpace d) := ih hU hUc hUW hf.le_succ
    have hs : U ∩ halfSpace d ⊆ W ∩ halfSpace d :=
      inter_subset_inter_left _ (subset_closure.trans hUW)
    exact upgrade_local (k + 1) B hU hV hVc hVU hu0 huU
      (hf.mono_set (by norm_num) (hU.inter isOpen_halfSpace) hs)
      (chosen_equation_restrict (hU.inter isOpen_halfSpace) hs
        (MemW1p.mono_set (hW.inter isOpen_halfSpace) inter_subset_right hu0.1) heq)

end Poincare.Analysis.Sobolev.BoundaryTangential
