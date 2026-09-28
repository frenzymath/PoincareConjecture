import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology RealInnerProductSpace ContDiff

namespace Poincare.RicciFlow.Splitting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private lemma isInvertible_of_isUnit {A : E →L[ℝ] E} (hA : IsUnit A) :
    A.IsInvertible := by
  rcases hA with ⟨e, rfl⟩
  exact ⟨ContinuousLinearEquiv.ofUnit e, rfl⟩

lemma isInvertible_add_kernel_projection (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) :
    (A + A.ker.starProjection).IsInvertible := by
  let K := A.ker
  let P := K.starProjection
  have hinj : Function.Injective (A + P) := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    change A x + P x = 0 at hx
    have hAP : A (P x) = 0 := (K.orthogonalProjectionOnto x).property
    have horth : inner ℝ (A x) (P x) = 0 := by
      calc
        inner ℝ (A x) (P x) = inner ℝ x (A (P x)) := hA x (P x)
        _ = 0 := by rw [hAP, inner_zero_right]
    have hP : P x = 0 := inner_self_eq_zero.mp (by
      calc
        inner ℝ (P x) (P x) = inner ℝ (A x + P x) (P x) := by
          rw [inner_add_left, horth, zero_add]
        _ = 0 := by rw [hx, inner_zero_left])
    have hAx : A x = 0 := by simpa [hP] using hx
    have hfix : P x = x := K.starProjection_mem_subspace_eq_self ⟨x, hAx⟩
    exact hfix.symm.trans hP
  apply isInvertible_of_isUnit
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

private lemma inverse_regularized_mem_kernel (A : E →L[ℝ] E)
    (K : Submodule ℝ E) (hB : (A + K.starProjection).IsInvertible)
    (hdim : Module.finrank ℝ A.ker = Module.finrank ℝ K) (c : K) :
    A ((A + K.starProjection).inverse c) = 0 := by
  let L : A.ker →ₗ[ℝ] K :=
    K.orthogonalProjectionOnto.toLinearMap.comp A.ker.subtype
  have hL : Function.Injective L := by
    intro x y hxy
    apply Subtype.ext
    apply hB.injective
    change A x + K.starProjection x = A y + K.starProjection y
    rw [show A x = 0 from x.property, show A y = 0 from y.property, zero_add, zero_add]
    exact congrArg Subtype.val hxy
  obtain ⟨z, hz⟩ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hL c
  have hsolve : (A + K.starProjection) z = c := by
    change A z + K.starProjection z = c
    rw [show A z = 0 from z.property, zero_add]
    exact congrArg Subtype.val hz
  rw [hB.inverse_apply_eq.mpr hsolve.symm]
  exact z.property

theorem exists_local_smooth_kernel_section
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : F → E →L[ℝ] E} {U : Set F} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) {p : F} (hp : p ∈ U)
    (hsym : (A p).toLinearMap.IsSymmetric)
    (hdim : ∀ q ∈ U, Module.finrank ℝ (A q).ker = Module.finrank ℝ (A p).ker)
    (v : E) (hv : A p v = 0) :
    ∃ (V : Set F) (s : F → E), IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ s V ∧ s p = v ∧ ∀ q ∈ V, A q (s q) = 0 := by
  let K := (A p).ker
  let B := fun q => A q + K.starProjection
  have hBp : (B p).IsInvertible := isInvertible_add_kernel_projection (A p) hsym
  have hnear : ∀ᶠ q in 𝓝 p, IsUnit (B q) :=
    ((hA.continuousOn.continuousAt (hU.mem_nhds hp)).add_const K.starProjection).eventually
      (Units.isOpen.mem_nhds (ContinuousLinearMap.isUnit_iff_bijective.mpr hBp.bijective))
  obtain ⟨V, hVB, hVo, hpV⟩ := mem_nhds_iff.mp hnear
  let W := V ∩ U
  have hB (q : F) (hq : q ∈ W) : (B q).IsInvertible :=
    isInvertible_of_isUnit (hVB hq.1)
  refine ⟨W, fun q => (B q).inverse v, hVo.inter hU, ⟨hpV, hp⟩,
    inter_subset_right, ?_, ?_, ?_⟩
  · intro q hq
    have hBq : ContDiffWithinAt ℝ ∞ B W q :=
      ((hA q hq.2).mono inter_subset_right).add contDiffWithinAt_const
    exact ((hB q hq).contDiffAt_map_inverse.comp_contDiffWithinAt q hBq).clm_apply
      contDiffWithinAt_const
  · apply hBp.inverse_apply_eq.mpr
    change v = A p v + K.starProjection v
    rw [hv, zero_add, K.starProjection_mem_subspace_eq_self ⟨v, hv⟩]
  · intro q hq
    exact inverse_regularized_mem_kernel (A q) K (hB q hq) (hdim q hq.2) ⟨v, hv⟩

private lemma regularized_section_hasDerivWithinAt_zero
    {A D : ℝ → E →L[ℝ] E} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJu : UniqueDiffWithinAt ℝ J t)
    (hA : HasDerivWithinAt A (D t) J t)
    (K : Submodule ℝ E)
    (hB : ∀ s ∈ J, (A s + K.starProjection).IsInvertible)
    (hdim : Module.finrank ℝ (A t).ker = Module.finrank ℝ K)
    (hann : ∀ v, A t v = 0 → D t v = 0) (c : K) :
    HasDerivWithinAt (fun s => (A s + K.starProjection).inverse c) 0 J t := by
  let B := fun s => A s + K.starProjection
  let y := fun s => (B s).inverse c
  have hBd : HasDerivWithinAt B (D t) J t := hA.add_const _
  have hyd : DifferentiableWithinAt ℝ y J t :=
    (((hB t ht).contDiffAt_map_inverse (n := 1)).differentiableAt (by simp)).comp_differentiableWithinAt
      t hBd.differentiableWithinAt |>.clm_apply (differentiableWithinAt_const (c : E))
  let dy := derivWithin y J t
  have hyD : HasDerivWithinAt y dy J t := hyd.hasDerivWithinAt
  have hprod := hBd.clm_apply hyD
  have hconst : HasDerivWithinAt (fun s => B s (y s)) 0 J t :=
    (hasDerivWithinAt_const t J (c : E)).congr_of_mem
      (fun s hs => (hB s hs).self_apply_inverse c) ht
  have hnull : A t (y t) = 0 :=
    inverse_regularized_mem_kernel (A t) K (hB t ht) hdim c
  have hzero : dy = 0 := by
    apply (hB t ht).injective
    have heq := (hprod.derivWithin hJu).symm.trans (hconst.derivWithin hJu)
    simpa only [hann (y t) hnull, zero_add, map_zero] using heq
  simpa only [hzero] using hyD

theorem kernel_eq_of_derivative_annihilates
    {A D : ℝ → E →L[ℝ] E} {J : Set ℝ} {k : ℕ}
    (hJ : Convex ℝ J) (hJu : UniqueDiffOn ℝ J)
    (hA : ∀ t ∈ J, HasDerivWithinAt A (D t) J t)
    (hsym : ∀ t ∈ J, (A t).toLinearMap.IsSymmetric)
    (hdim : ∀ t ∈ J, Module.finrank ℝ (A t).ker = k)
    (hann : ∀ t ∈ J, ∀ v, A t v = 0 → D t v = 0)
    {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    (A s).ker = (A t).ker := by
  have hlocal (t : ℝ) (ht : t ∈ J) :
      ∃ r > 0, ∀ s ∈ Metric.ball t r ∩ J, (A s).ker = (A t).ker := by
    let K := (A t).ker
    let B := fun s => A s + K.starProjection
    have hBt : (B t).IsInvertible := isInvertible_add_kernel_projection (A t) (hsym t ht)
    have hnear : ∀ᶠ s in 𝓝[J] t, IsUnit (B s) :=
      ((hA t ht).continuousWithinAt.add_const K.starProjection).eventually
        (Units.isOpen.mem_nhds (ContinuousLinearMap.isUnit_iff_bijective.mpr hBt.bijective))
    obtain ⟨r, hr, hrad⟩ := Metric.mem_nhdsWithin_iff.mp hnear
    let V := J ∩ Metric.ball t r
    have hV : Convex ℝ V := hJ.inter (convex_ball t r)
    have hVu : UniqueDiffOn ℝ V := hJu.inter Metric.isOpen_ball
    have htV : t ∈ V := ⟨ht, Metric.mem_ball_self hr⟩
    have hB (q : ℝ) (hq : q ∈ V) : (B q).IsInvertible :=
      isInvertible_of_isUnit (hrad ⟨hq.2, hq.1⟩)
    have hsection (c : K) (q : ℝ) (hq : q ∈ V) :
        (B q).inverse c = (B t).inverse c := by
      have hd (z : ℝ) (hz : z ∈ V) :
          HasDerivWithinAt (fun w => (B w).inverse c) 0 V z :=
        regularized_section_hasDerivWithinAt_zero hz (hVu z hz)
          ((hA z hz.1).mono inter_subset_left) K hB
          ((hdim z hz.1).trans (hdim t ht).symm) (hann z hz.1) c
      have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        hd (fun z hz => le_refl ‖(0 : E)‖) hV htV hq
      simpa only [norm_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] using hbound
    refine ⟨r, hr, ?_⟩
    intro q hq
    have hqV : q ∈ V := ⟨hq.2, hq.1⟩
    have hle : K ≤ (A q).ker := by
      intro c hc
      have hfix : (B t).inverse c = c := hBt.inverse_apply_eq.mpr (by
        change c = A t c + K.starProjection c
        rw [show A t c = 0 from hc, zero_add,
          K.starProjection_mem_subspace_eq_self ⟨c, hc⟩])
      have heq : (B q).inverse c = c := (hsection ⟨c, hc⟩ q hqV).trans hfix
      have hnull := inverse_regularized_mem_kernel (A q) K (hB q hqV)
        ((hdim q hq.2).trans (hdim t ht).symm) ⟨c, hc⟩
      rwa [heq] at hnull
    exact (Submodule.eq_of_le_of_finrank_eq hle
      ((hdim t ht).trans (hdim q hq.2).symm)).symm
  let K : J → Submodule ℝ E := fun q => (A q).ker
  have hK : IsLocallyConstant K := by
    apply (IsLocallyConstant.iff_eventually_eq K).mpr
    intro p
    obtain ⟨r, hr, hloc⟩ := hlocal p p.property
    have hnear : ∀ᶠ q : J in 𝓝 p, (q : ℝ) ∈ Metric.ball p.val r :=
      (continuous_subtype_val.tendsto p).eventually (Metric.ball_mem_nhds p.val hr)
    filter_upwards [hnear] with q hq
    exact hloc q ⟨hq, q.property⟩
  let : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp hJ.isPreconnected
  exact hK.apply_eq_of_preconnectedSpace ⟨s, hs⟩ ⟨t, ht⟩

end Poincare.RicciFlow.Splitting
