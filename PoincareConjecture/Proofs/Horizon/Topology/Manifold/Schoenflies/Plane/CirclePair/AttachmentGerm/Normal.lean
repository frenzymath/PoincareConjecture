import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.CollarExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.CircleAttachmentGerm

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

theorem exists_disk_diffeomorph_of_circle_fixing_germ
    (k : E2 → E2) (hk : ContDiff Real ∞ k) (p : S1)
    (hfix : ∀ᶠ x in 𝓝 (p : E2), x ∈ sphere (0 : E2) 1 → k x = x)
    (hnormal : 0 < inner Real (p : E2) (fderiv Real k p p)) :
    ∃ G : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      G '' closedBall (0 : E2) 1 = closedBall (0 : E2) 1 ∧
      G '' ball (0 : E2) 1 = ball (0 : E2) 1 ∧
      (∀ q : S1, G q = q) ∧ (G : E2 → E2) =ᶠ[𝓝 (p : E2)] k := by
  have hncont : Continuous (fun x : E2 => inner Real x (fderiv Real k x x)) :=
    continuous_id.inner ((hk.continuous_fderiv (by simp)).clm_apply continuous_id)
  have hn : ∀ᶠ x in 𝓝 (p : E2), 0 < inner Real x (fderiv Real k x x) :=
    hncont.continuousAt.eventually (lt_mem_nhds hnormal)
  obtain ⟨a, ha, haball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (inter_mem hfix hn)
  let χ : ContDiffBump (p : E2) := ⟨a / 2, a, by positivity, by linarith⟩
  let e : E2 → E2 := fun x => x + χ x • (k x - x)
  have he : ContDiff Real ∞ e := contDiff_id.add (χ.contDiff.smul (hk.sub contDiff_id))
  have heoutside (x : E2) (hx : x ∉ closedBall (p : E2) a) :
      e =ᶠ[𝓝 x] id := by
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
    have hχ : χ y = 0 := χ.zero_of_le_dist (le_of_lt (not_le.mp hy))
    simp [e, hχ]
  have hefix (q : S1) : e q = q := by
    by_cases hq : (q : E2) ∈ closedBall (p : E2) a
    · simp [e, (haball hq).1 q.property]
    · exact (heoutside q hq).eq_of_nhds
  have henormal (q : S1) : 0 < inner Real (q : E2) (fderiv Real e q q) := by
    by_cases hq : (q : E2) ∈ closedBall (p : E2) a
    · have hkq := (haball hq).1 q.property
      have hd : fderiv Real e q = ContinuousLinearMap.id Real E2 +
          χ q • (fderiv Real k q - ContinuousLinearMap.id Real E2) := by
        have hχsmooth : ContDiff Real ∞ χ := χ.contDiff
        have hχd := hχsmooth.differentiable (by simp) (q : E2)
        have hkd := hk.differentiable (by simp) (q : E2)
        have hde := (hasFDerivAt_id (q : E2)).add
          (hχd.hasFDerivAt.smul (hkd.hasFDerivAt.sub (hasFDerivAt_id (q : E2))))
        simpa +instances [e, hkq, Pi.add_def, Pi.smul_def, Pi.sub_def] using hde.fderiv
      rw [hd]
      simp only [add_apply, smul_apply, sub_apply, ContinuousLinearMap.id_apply,
        inner_add_right, inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq,
        norm_eq_of_mem_sphere, one_pow]
      have hkn := (haball hq).2
      rcases eq_or_lt_of_le (χ.nonneg (x := (q : E2))) with hzero | hpos
      · rw [← hzero]
        norm_num
      · have hmul := mul_pos hpos hkn
        have hle := χ.le_one (x := (q : E2))
        nlinarith
    · rw [(heoutside q hq).fderiv_eq]
      simp
  obtain ⟨ε, hε, _, _, _, _, G, _, hGe, hGfix, hGclosed, hGball⟩ :=
    exists_ambient_circle_collar_extension he hefix henormal isOpen_univ (subset_univ _)
  have heq : e =ᶠ[𝓝 (p : E2)] k := by
    filter_upwards [χ.eventuallyEq_one] with x hx
    simp [e, hx]
  have hband : ∀ᶠ x in 𝓝 (p : E2), |‖x‖ - 1| < ε := by
    have hc : ContinuousAt (fun x : E2 => |‖x‖ - 1|) p := by fun_prop
    exact hc.eventually (gt_mem_nhds (by simpa using hε))
  refine ⟨G, hGclosed, hGball, hGfix, ?_⟩
  filter_upwards [heq, hband] with x hx hxband
  exact (hGe x hxband).trans hx

end Poincare.Manifold.Schoenflies.CircleAttachmentGerm
