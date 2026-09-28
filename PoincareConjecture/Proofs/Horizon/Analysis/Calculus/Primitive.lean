import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.DividedDifferences
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Extension.Compact










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Topology Interval

namespace Poincare.Analysis

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


def radialPrimitive (α : E → E →L[ℝ] ℝ) (a x : E) : ℝ :=
  ∫ t in (0 : ℝ)..1, α (a + t • (x - a)) (x - a)


theorem contDiff_radialPrimitive {α : E → E →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (a : E) : ContDiff ℝ ∞ (radialPrimitive α a) := by
  unfold radialPrimitive
  apply contDiff_parameter_intervalIntegral_of_contDiff
    (F := fun p : E × ℝ => α (a + p.2 • (p.1 - a)) (p.1 - a))
  exact (hα.comp (contDiff_const.add
    (contDiff_snd.smul (contDiff_fst.sub contDiff_const)))).clm_apply
      (contDiff_fst.sub contDiff_const)



theorem hasFDerivAt_radialPrimitive {α : E → E →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (a x : E)
    (hclosed : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u v : E,
      fderiv ℝ α (a + t • (x - a)) u v =
        fderiv ℝ α (a + t • (x - a)) v u) :
    HasFDerivAt (radialPrimitive α a) (α x) x := by
  let F : E × ℝ → ℝ := fun p => α (a + p.2 • (p.1 - a)) (p.1 - a)
  have hF : ContDiff ℝ ∞ F :=
    (hα.comp (contDiff_const.add
      (contDiff_snd.smul (contDiff_fst.sub contDiff_const)))).clm_apply
        (contDiff_fst.sub contDiff_const)
  let L : ℝ → E →L[ℝ] ℝ := fun t =>
    α (a + t • (x - a)) + t • (fderiv ℝ α (a + t • (x - a))).flip (x - a)
  have hL : Continuous L := by
    have hd : Continuous (fderiv ℝ α) :=
      (hα.fderiv_right (show ∞ + 1 ≤ (∞ : ℕ∞ω) by simp)).continuous
    have hflip : Continuous (fun A : E →L[ℝ] E →L[ℝ] ℝ => A.flip) :=
      (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous
    exact (hα.continuous.comp (continuous_const.add
      (continuous_id.smul continuous_const))).add
      (continuous_id.smul ((hflip.comp (hd.comp (continuous_const.add
        (continuous_id.smul continuous_const)))).clm_apply continuous_const))
  have hpartial (t : ℝ) :
      (fderiv ℝ F (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ) = L t := by
    have hinner : HasFDerivAt (fun y : E => a + t • (y - a))
        (t • ContinuousLinearMap.id ℝ E) x := by
      simpa using (((hasFDerivAt_id x).sub_const a).const_smul t).const_add a
    have hv := (((hα.differentiable (by simp)) _).hasFDerivAt.comp x hinner).clm_apply
      ((hasFDerivAt_id x).sub_const a)
    have hp : HasFDerivAt (fun y : E => F (y, t))
        ((fderiv ℝ F (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
      have hDF : HasFDerivAt F (fderiv ℝ F (x, t)) (x, t) :=
        ((hF.differentiable (by simp)) (x, t)).hasFDerivAt
      exact hDF.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
    have he := hp.unique hv
    rw [he]
    ext v
    simp [L]
  have hd := hasFDerivAt_parameter_intervalIntegral_of_contDiff hF 0 1 x
  change HasFDerivAt (radialPrimitive α a)
    (∫ t in (0 : ℝ)..1, (fderiv ℝ F (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x at hd
  simp_rw [hpartial] at hd
  convert hd using 1
  ext v
  rw [ContinuousLinearMap.intervalIntegral_apply (hL.intervalIntegrable 0 1)]
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => s * α (a + s • (x - a)) v) (L t v) t := by
    have hi : HasDerivAt (fun s : ℝ => a + s • (x - a)) (x - a) t := by
      simpa using ((hasDerivAt_id t).smul_const (x - a)).const_add a
    have hαt := (((hα.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t hi).clm_apply
      (hasDerivAt_const t v)
    convert! (hasDerivAt_id t).mul hαt using 1
    simp only [L, add_apply, smul_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul, one_mul, map_zero, add_zero, id_eq,
      Function.comp_apply]
    rw [hclosed t ht v (x - a)]
  have hcalc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hderiv t (by simpa using ht))
    ((hL.clm_apply continuous_const).intervalIntegrable 0 1)
  simpa using hcalc.symm


theorem fderiv_radialPrimitive_eqOn {α : E → E →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) {U : Set E} (hU : Convex ℝ U) {a : E} (ha : a ∈ U)
    (hclosed : ∀ x ∈ U, ∀ u v : E, fderiv ℝ α x u v = fderiv ℝ α x v u) :
    EqOn (fderiv ℝ (radialPrimitive α a)) α U := by
  intro x hx
  apply (hasFDerivAt_radialPrimitive hα a x _).fderiv
  intro t ht u v
  exact hclosed (a + t • (x - a))
    (hU.add_smul_sub_mem ha hx ht) u v



theorem exists_local_primitive_of_fderiv_symmetric {α : E → E →L[ℝ] ℝ}
    {U : Set E} (hU : IsOpen U) (hα : ContDiffOn ℝ ∞ α U)
    (hclosed : ∀ x ∈ U, ∀ u v : E, fderiv ℝ α x u v = fderiv ℝ α x v u)
    {a : E} (ha : a ∈ U) (c : ℝ) :
    ∃ (r : ℝ) (f : E → ℝ), 0 < r ∧ Metric.ball a r ⊆ U ∧
      ContDiff ℝ ∞ f ∧ f a = c ∧
      ∀ x ∈ Metric.ball a r, HasFDerivAt f (α x) x := by
  obtain ⟨β, V, hβ, hV, haV, hVU, heq⟩ :=
    exists_contDiff_extension_near_compact isCompact_singleton hU
      (singleton_subset_iff.mpr ha) α hα
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp
    (hV.mem_nhds (haV (mem_singleton a)))
  have hsymm (x : E) (hx : x ∈ Metric.ball a r) (u v : E) :
      fderiv ℝ β x u v = fderiv ℝ β x v u := by
    rw [(heq.eventuallyEq_of_mem (hV.mem_nhds (hrV hx))).fderiv_eq]
    exact hclosed x (hVU (hrV hx)) u v
  refine ⟨r, fun x => radialPrimitive β a x + c, hr, hrV.trans hVU,
    (contDiff_radialPrimitive hβ a).add contDiff_const, ?_, ?_⟩
  · simp [radialPrimitive]
  · intro x hx
    have hderiv := hasFDerivAt_radialPrimitive hβ a x (fun t ht u v =>
      hsymm (a + t • (x - a))
        ((convex_ball a r).add_smul_sub_mem (Metric.mem_ball_self hr) hx ht) u v)
    simpa [heq (hrV hx)] using hderiv.add_const c

end Poincare.Analysis
