import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric IsManifold
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.SphereCharts

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

attribute [-simp] AddSubgroupClass.coe_norm Submodule.coe_norm in
private theorem stereoToFun_neg_stereoInvFun {v : E4} (hv : ‖v‖ = 1)
    (w : (ℝ ∙ v)ᗮ) (hw : w ≠ 0) :
    stereoToFun v (-(stereoInvFun hv w : E4)) = -(4 / ‖w‖ ^ 2) • w := by
  have hn : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  have hd : ‖w‖ ^ 2 + 4 ≠ 0 := by positivity
  have h₁ : (ℝ ∙ v)ᗮ.orthogonalProjectionOnto v = 0 :=
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero v
  have h₂ : ⟪v, w⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
  have h₃ : ⟪v, v⟫_ℝ = 1 := by simp [hv]
  simp only [stereoToFun, stereoInvFun_apply, map_neg, innerSL_apply_apply,
    smul_add, map_add, map_smul,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, h₁, h₂, h₃,
    smul_zero, add_zero]
  match_scalars
  simp only [smul_eq_mul, mul_one, zero_add, sub_neg_eq_add]
  field_simp [hn, hd, norm_ne_zero_iff.mpr hw]
  ring_nf

private theorem threeSphereStereographic_neg_symm (v : UnitThreeSphere)
    (x : E3) (hx : x ≠ 0) :
    threeSphereStereographic v (-((threeSphereStereographic v).symm x)) =
      -(4 / ‖x‖ ^ 2) • x := by
  let : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩
  let U : (ℝ ∙ (v : E4))ᗮ ≃ₗᵢ[ℝ] E3 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 3
      (ne_zero_of_mem_unit_sphere v)).repr
  have hu : U.symm x ≠ 0 := by
    intro h
    apply hx
    simpa using congrArg U h
  change U (stereoToFun (v : E4)
    (-(stereoInvFun (norm_eq_of_mem_sphere v) (U.symm x) : E4))) = _
  rw [stereoToFun_neg_stereoInvFun _ _ hu]
  simp

private noncomputable def halfScale : E3 ≃ₜ E3 :=
  Homeomorph.smulOfNeZero (1 / 2 : ℝ) (by norm_num)

noncomputable def radialSphereChart (v : UnitThreeSphere) :
    OpenPartialHomeomorph UnitThreeSphere E3 :=
  (threeSphereStereographic v).trans halfScale.toOpenPartialHomeomorph

noncomputable def oppositeRadialSphereChart (v : UnitThreeSphere) :
    OpenPartialHomeomorph UnitThreeSphere E3 :=
  ((Homeomorph.neg UnitThreeSphere).toOpenPartialHomeomorph.trans
    (radialSphereChart v)).trans (Homeomorph.neg E3).toOpenPartialHomeomorph

@[simp] theorem radialSphereChart_source (v : UnitThreeSphere) :
    (radialSphereChart v).source = {v}ᶜ := by
  simp [radialSphereChart]

@[simp] theorem radialSphereChart_target (v : UnitThreeSphere) :
    (radialSphereChart v).target = univ := by
  simp [radialSphereChart, halfScale]

@[simp] theorem radialSphereChart_apply (v x : UnitThreeSphere) :
    radialSphereChart v x = (1 / 2 : ℝ) • threeSphereStereographic v x := rfl

@[simp] theorem radialSphereChart_symm_apply (v : UnitThreeSphere) (x : E3) :
    (radialSphereChart v).symm x = (threeSphereStereographic v).symm ((2 : ℝ) • x) := by
  simp [radialSphereChart, halfScale]

@[simp] theorem oppositeRadialSphereChart_apply (v x : UnitThreeSphere) :
    oppositeRadialSphereChart v x = -(radialSphereChart v (-x)) := rfl

@[simp] theorem oppositeRadialSphereChart_source (v : UnitThreeSphere) :
    (oppositeRadialSphereChart v).source = {-v}ᶜ := by
  ext x
  simp [oppositeRadialSphereChart]

@[simp] theorem oppositeRadialSphereChart_target (v : UnitThreeSphere) :
    (oppositeRadialSphereChart v).target = univ := by
  simp [oppositeRadialSphereChart]

theorem radialSphereChart_source_union (v : UnitThreeSphere) :
    (radialSphereChart v).source ∪ (oppositeRadialSphereChart v).source = univ := by
  simpa using threeSphereStereographic_source_union_antipode v

theorem radialSphereChart_transition (v : UnitThreeSphere) (x : E3) (hx : x ≠ 0) :
    oppositeRadialSphereChart v ((radialSphereChart v).symm x) =
      (‖x‖ ^ 2)⁻¹ • x := by
  have htwo : (2 : ℝ) • x ≠ 0 := smul_ne_zero (by norm_num) hx
  rw [oppositeRadialSphereChart_apply, radialSphereChart_apply,
    radialSphereChart_symm_apply, threeSphereStereographic_neg_symm v _ htwo]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  match_scalars
  field_simp
  ring

theorem radialSphereChart_transition_exp (v : UnitThreeSphere)
    (q : UnitTwoSphere) (t : ℝ) :
    oppositeRadialSphereChart v
      ((radialSphereChart v).symm (Real.exp t • (q : E3))) =
        Real.exp (-t) • (q : E3) := by
  rw [radialSphereChart_transition v _
    (smul_ne_zero (Real.exp_ne_zero t) (ne_zero_of_mem_unit_sphere q))]
  simp only [norm_smul, Real.norm_eq_abs, Real.abs_exp, norm_eq_of_mem_sphere,
    mul_one, smul_smul, Real.exp_neg]
  congr 1
  field_simp

theorem radialSphereChart_transition_norm (v : UnitThreeSphere)
    (x : E3) (hx : x ≠ 0) :
    ‖oppositeRadialSphereChart v ((radialSphereChart v).symm x)‖ = ‖x‖⁻¹ := by
  rw [radialSphereChart_transition v x hx, norm_smul]
  simp only [Real.norm_eq_abs, abs_inv, abs_pow, abs_norm]
  field_simp

@[simp] theorem radialSphereChart_symm_zero (v : UnitThreeSphere) :
    (radialSphereChart v).symm 0 = -v := by simp

theorem radialSphereChart_transition_source (v : UnitThreeSphere) :
    ((radialSphereChart v).symm.trans (oppositeRadialSphereChart v)).source =
      ({0} : Set E3)ᶜ := by
  ext x
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    radialSphereChart_target, oppositeRadialSphereChart_source, mem_inter_iff,
    mem_univ, true_and, mem_preimage, mem_compl_iff, mem_singleton_iff]
  constructor
  · intro hx hzero
    exact hx (hzero ▸ radialSphereChart_symm_zero v)
  · intro hx heq
    apply hx
    have h := congrArg (radialSphereChart v) heq
    rw [(radialSphereChart v).right_inv (by simp)] at h
    simpa using h

theorem contMDiffOn_radialSphereChart (v : UnitThreeSphere) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (radialSphereChart v)
      (radialSphereChart v).source := by
  have h := contMDiffOn_of_mem_maximalAtlas
    (threeSphereStereographic_mem_maximalAtlas v)
  have hs : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : E3 => (1 / 2 : ℝ) • x) :=
    (contDiff_id.const_smul (1 / 2 : ℝ)).contMDiff
  rw [show ⇑(radialSphereChart v) =
    (fun x => (1 / 2 : ℝ) • threeSphereStereographic v x) from rfl,
    radialSphereChart_source]
  simpa only [Function.comp_def, threeSphereStereographic_source] using
    hs.comp_contMDiffOn h

theorem contMDiffOn_radialSphereChart_symm (v : UnitThreeSphere) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (radialSphereChart v).symm
      (radialSphereChart v).target := by
  have h := contMDiffOn_symm_of_mem_maximalAtlas
    (threeSphereStereographic_mem_maximalAtlas v)
  rw [threeSphereStereographic_target, contMDiffOn_univ] at h
  have hs : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : E3 => (2 : ℝ) • x) :=
    (contDiff_id.const_smul (2 : ℝ)).contMDiff
  rw [show ⇑(radialSphereChart v).symm =
    (fun x => (threeSphereStereographic v).symm ((2 : ℝ) • x)) from
      funext (radialSphereChart_symm_apply v), radialSphereChart_target,
    contMDiffOn_univ]
  exact h.comp hs

theorem contMDiffOn_oppositeRadialSphereChart (v : UnitThreeSphere) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (oppositeRadialSphereChart v)
      (oppositeRadialSphereChart v).source := by
  let : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩
  have hn : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : UnitThreeSphere => -x) :=
    contMDiff_neg_sphere
  have hm : MapsTo (fun x : UnitThreeSphere => -x)
      (oppositeRadialSphereChart v).source (radialSphereChart v).source := by
    intro x hx
    simpa [neg_eq_iff_eq_neg] using hx
  exact (contDiff_neg.contMDiff.comp_contMDiffOn
    ((contMDiffOn_radialSphereChart v).comp hn.contMDiffOn hm))

theorem contMDiffOn_oppositeRadialSphereChart_symm (v : UnitThreeSphere) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (oppositeRadialSphereChart v).symm
      (oppositeRadialSphereChart v).target := by
  let : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩
  have h := contMDiffOn_radialSphereChart_symm v
  rw [radialSphereChart_target, contMDiffOn_univ] at h
  have hn : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : UnitThreeSphere => -x) :=
    contMDiff_neg_sphere
  rw [oppositeRadialSphereChart_target, contMDiffOn_univ]
  exact hn.comp (h.comp contDiff_neg.contMDiff)

private theorem trans_ofSet_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) (s : Set Y) (hs : IsOpen s) (x : X) :
    (e.trans (OpenPartialHomeomorph.ofSet s hs)) x = e x := rfl

private theorem trans_ofSet_symm_apply {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y) (s : Set Y) (hs : IsOpen s)
    (x : Y) : (e.trans (OpenPartialHomeomorph.ofSet s hs)).symm x = e.symm x := rfl

noncomputable def radialSphereBallChart (v : UnitThreeSphere) (r : ℝ) :
    OpenPartialHomeomorph UnitThreeSphere E3 :=
  (radialSphereChart v).trans (OpenPartialHomeomorph.ofSet (ball 0 (Real.exp r)) isOpen_ball)

noncomputable def oppositeRadialSphereBallChart (v : UnitThreeSphere) (r : ℝ) :
    OpenPartialHomeomorph UnitThreeSphere E3 :=
  (oppositeRadialSphereChart v).trans
    (OpenPartialHomeomorph.ofSet (ball 0 (Real.exp r)) isOpen_ball)

@[simp] theorem radialSphereBallChart_source (v : UnitThreeSphere) (r : ℝ) :
    (radialSphereBallChart v r).source =
      (radialSphereChart v).source ∩ (radialSphereChart v) ⁻¹' ball 0 (Real.exp r) :=
  rfl

@[simp] theorem radialSphereBallChart_target (v : UnitThreeSphere) (r : ℝ) :
    (radialSphereBallChart v r).target = ball 0 (Real.exp r) := by
  simp [radialSphereBallChart]

@[simp] theorem oppositeRadialSphereBallChart_source (v : UnitThreeSphere) (r : ℝ) :
    (oppositeRadialSphereBallChart v r).source =
      (oppositeRadialSphereChart v).source ∩
        (oppositeRadialSphereChart v) ⁻¹' ball 0 (Real.exp r) := rfl

@[simp] theorem oppositeRadialSphereBallChart_target (v : UnitThreeSphere) (r : ℝ) :
    (oppositeRadialSphereBallChart v r).target = ball 0 (Real.exp r) := by
  simp [oppositeRadialSphereBallChart]

@[simp] theorem radialSphereBallChart_apply (v x : UnitThreeSphere) (r : ℝ) :
    radialSphereBallChart v r x = radialSphereChart v x :=
  trans_ofSet_apply _ _ _ x

@[simp] theorem radialSphereBallChart_symm_apply (v : UnitThreeSphere) (r : ℝ)
    (x : E3) : (radialSphereBallChart v r).symm x = (radialSphereChart v).symm x :=
  trans_ofSet_symm_apply _ _ _ x

@[simp] theorem oppositeRadialSphereBallChart_apply (v x : UnitThreeSphere) (r : ℝ) :
    oppositeRadialSphereBallChart v r x = oppositeRadialSphereChart v x :=
  trans_ofSet_apply _ _ _ x

@[simp] theorem oppositeRadialSphereBallChart_symm_apply (v : UnitThreeSphere) (r : ℝ)
    (x : E3) :
    (oppositeRadialSphereBallChart v r).symm x =
      (oppositeRadialSphereChart v).symm x :=
  trans_ofSet_symm_apply _ _ _ x

theorem radialSphereBallChart_source_union (v : UnitThreeSphere) (r : ℝ) (hr : 0 < r) :
    (radialSphereBallChart v r).source ∪
      (oppositeRadialSphereBallChart v r).source = univ := by
  have hR : 1 < Real.exp r := Real.one_lt_exp_iff.mpr hr
  apply eq_univ_of_forall
  intro p
  by_cases hp : p = v
  · right
    subst p
    simp only [oppositeRadialSphereBallChart_source, oppositeRadialSphereChart_source,
      mem_inter_iff, mem_compl_iff, mem_singleton_iff, mem_preimage]
    refine ⟨ne_neg_of_mem_unit_sphere ℝ v, ?_⟩
    simpa using Real.exp_pos r
  have hps : p ∈ (radialSphereChart v).source := by simpa using hp
  by_cases hy : ‖radialSphereChart v p‖ < Real.exp r
  · left
    rw [radialSphereBallChart_source]
    exact ⟨hps, mem_ball_zero_iff.mpr hy⟩
  right
  rw [oppositeRadialSphereBallChart_source]
  have hyn : Real.exp r ≤ ‖radialSphereChart v p‖ := le_of_not_gt hy
  have hy0 : radialSphereChart v p ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt ((Real.exp_pos r).trans_le hyn))
  have hother : p ∈ (oppositeRadialSphereChart v).source := by
    have ht : radialSphereChart v p ∈
        ((radialSphereChart v).symm.trans (oppositeRadialSphereChart v)).source := by
      rw [radialSphereChart_transition_source]
      exact hy0
    simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage,
      (radialSphereChart v).left_inv hps] using ht.2
  refine ⟨hother, mem_ball_zero_iff.mpr ?_⟩
  have hn : ‖oppositeRadialSphereChart v p‖ = ‖radialSphereChart v p‖⁻¹ := by
    simpa only [(radialSphereChart v).left_inv hps] using
      radialSphereChart_transition_norm v (radialSphereChart v p) hy0
  rw [hn]
  have hyle : 1 ≤ ‖radialSphereChart v p‖ := hR.le.trans hyn
  exact ((inv_le_one₀ ((Real.exp_pos r).trans_le hyn)).mpr hyle).trans_lt hR

theorem radialSphereBallChart_transition_source (v : UnitThreeSphere) (r : ℝ) :
    ((radialSphereBallChart v r).symm.trans
      (oppositeRadialSphereBallChart v r)).source =
        {x : E3 | Real.exp (-r) < ‖x‖ ∧ ‖x‖ < Real.exp r} := by
  ext x
  have hfull : (radialSphereChart v).symm x ∈ (oppositeRadialSphereChart v).source ↔
      x ≠ 0 := by
    have := congrArg (fun s : Set E3 => x ∈ s) (radialSphereChart_transition_source v)
    simpa only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      radialSphereChart_target, mem_inter_iff, mem_univ, true_and, mem_preimage,
      mem_compl_iff, mem_singleton_iff] using this.to_iff
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    radialSphereBallChart_target, oppositeRadialSphereBallChart_source,
    radialSphereBallChart_symm_apply, mem_inter_iff, mem_preimage,
    mem_ball_zero_iff, mem_ofPred_eq, hfull]
  constructor
  · rintro ⟨hxR, hx0, hxinv⟩
    rw [radialSphereChart_transition_norm v x hx0] at hxinv
    refine ⟨?_, hxR⟩
    rw [Real.exp_neg]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr hx0) (Real.exp_pos r)).mp hxinv
  · rintro ⟨hxr, hxR⟩
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt ((Real.exp_pos (-r)).trans hxr))
    refine ⟨hxR, hx0, ?_⟩
    rw [radialSphereChart_transition_norm v x hx0]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr hx0) (Real.exp_pos r)).mpr
      (by simpa only [Real.exp_neg] using hxr)

theorem radialSphereBallChart_transition (v : UnitThreeSphere) (r : ℝ)
    (x : E3) (hx : x ≠ 0) :
    oppositeRadialSphereBallChart v r ((radialSphereBallChart v r).symm x) =
      (‖x‖ ^ 2)⁻¹ • x :=
  by simpa only [oppositeRadialSphereBallChart_apply, radialSphereBallChart_symm_apply]
    using radialSphereChart_transition v x hx

theorem radialSphereBallChart_contMDiff (v : UnitThreeSphere) (r : ℝ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (radialSphereBallChart v r)
      (radialSphereBallChart v r).source ∧
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (radialSphereBallChart v r).symm
      (radialSphereBallChart v r).target := by
  constructor
  · rw [show ⇑(radialSphereBallChart v r) = radialSphereChart v from
      funext (fun x => radialSphereBallChart_apply v x r), radialSphereBallChart_source]
    exact (contMDiffOn_radialSphereChart v).mono inter_subset_left
  · rw [show ⇑(radialSphereBallChart v r).symm = (radialSphereChart v).symm from
      funext (radialSphereBallChart_symm_apply v r)]
    exact (contMDiffOn_radialSphereChart_symm v).mono (by simp)

theorem oppositeRadialSphereBallChart_contMDiff (v : UnitThreeSphere) (r : ℝ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (oppositeRadialSphereBallChart v r)
      (oppositeRadialSphereBallChart v r).source ∧
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (oppositeRadialSphereBallChart v r).symm
      (oppositeRadialSphereBallChart v r).target := by
  constructor
  · rw [show ⇑(oppositeRadialSphereBallChart v r) = oppositeRadialSphereChart v from
      funext (fun x => oppositeRadialSphereBallChart_apply v x r),
      oppositeRadialSphereBallChart_source]
    exact (contMDiffOn_oppositeRadialSphereChart v).mono inter_subset_left
  · rw [show ⇑(oppositeRadialSphereBallChart v r).symm =
      (oppositeRadialSphereChart v).symm from
        funext (oppositeRadialSphereBallChart_symm_apply v r)]
    exact (contMDiffOn_oppositeRadialSphereChart_symm v).mono (by simp)

theorem exists_diffeomorph_unitThreeSphere_of_radial_balls
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace E3 Y]
    (e₀ e₁ : OpenPartialHomeomorph Y E3) (v : UnitThreeSphere)
    (r : ℝ) (hr : 0 < r)
    (hcover : e₀.source ∪ e₁.source = univ)
    (htarget₀ : e₀.target = ball 0 (Real.exp r))
    (htarget₁ : e₁.target = ball 0 (Real.exp r))
    (he₀ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e₀ e₀.source)
    (he₁ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e₁ e₁.source)
    (hei₀ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e₀.symm e₀.target)
    (hei₁ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e₁.symm e₁.target)
    (hsource : (e₀.symm.trans e₁).source =
      {x : E3 | Real.exp (-r) < ‖x‖ ∧ ‖x‖ < Real.exp r})
    (htransition : ∀ x ∈ (e₀.symm.trans e₁).source,
      e₁ (e₀.symm x) = (‖x‖ ^ 2)⁻¹ • x) :
    ∃ d : Diffeomorph (𝓡 3) (𝓡 3) Y UnitThreeSphere ∞,
      EqOn d ((radialSphereBallChart v r).symm ∘ e₀) e₀.source ∧
      EqOn d ((oppositeRadialSphereBallChart v r).symm ∘ e₁) e₁.source ∧
      EqOn d.symm (e₀.symm ∘ radialSphereBallChart v r)
        (radialSphereBallChart v r).source ∧
      EqOn d.symm (e₁.symm ∘ oppositeRadialSphereBallChart v r)
        (oppositeRadialSphereBallChart v r).source := by
  refine OpenPartialHomeomorph.exists_diffeomorph_of_chart_transition e₀ e₁
    (radialSphereBallChart v r) (oppositeRadialSphereBallChart v r) hcover
    (radialSphereBallChart_source_union v r hr)
    (htarget₀.trans (radialSphereBallChart_target v r).symm)
    (htarget₁.trans (oppositeRadialSphereBallChart_target v r).symm)
    he₀ he₁ hei₀ hei₁ (radialSphereBallChart_contMDiff v r).1
    (oppositeRadialSphereBallChart_contMDiff v r).1
    (radialSphereBallChart_contMDiff v r).2
    (oppositeRadialSphereBallChart_contMDiff v r).2 ⟨?_, ?_⟩
  · exact hsource.trans (radialSphereBallChart_transition_source v r).symm
  · intro x hx
    have hxnorm : Real.exp (-r) < ‖x‖ := (hsource ▸ hx).1
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt ((Real.exp_pos (-r)).trans hxnorm))
    exact (htransition x hx).trans (radialSphereBallChart_transition v r x hx0).symm

end PoincareConjecture.SphereCharts
