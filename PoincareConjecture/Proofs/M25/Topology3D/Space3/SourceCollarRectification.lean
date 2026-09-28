import PoincareConjecture.Proofs.M25.Topology3D.Space3.CircleRadialChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.OrientedCollarCorrection













set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D


noncomputable def radiusToCollarTime (k : ℝ) (hk : k ≠ 0) :
    Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toEquiv := {
    toFun := fun r => k * (1 - r)
    invFun := fun t => 1 - t / k
    left_inv := fun r => by field_simp; ring
    right_inv := fun t => by field_simp; ring }
  contMDiff_toFun := (contDiff_const.mul (contDiff_const.sub contDiff_id)).contMDiff
  contMDiff_invFun := (contDiff_const.sub (contDiff_id.div_const k)).contMDiff



theorem source_disc_collar_rectification
    (Q : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere)
    (hQ : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ Q Q.source)
    (hQi : ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ Q.symm Q.target)
    {d : ℝ} (hd : 0 < d) (hQs : Q.source = univ ×ˢ Ioo (-d) d)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : closedBall 0 1 ⊆ e.source)
    (hem : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target)
    (hb : ∀ θ : UnitCircle, e θ.1 = Q (θ, 0))
    (hneg : ∀ θ : UnitCircle, ∀ s ∈ Ioo (-d) d,
      s ≤ 0 → Q (θ, s) ∉ e '' ball 0 1)
    {k : ℝ} (hk : 0 < k) :
    ∃ F : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞,
      F '' ball 0 1 = ball 0 1 ∧ F '' closedBall 0 1 = closedBall 0 1 ∧
      (∀ θ : UnitCircle, F θ.1 = θ.1) ∧
      ∀ᶠ x in 𝓝ˢ (sphere (0 : E2) 1),
        F x ∈ e.source ∧ e (F x) = Q (circleDirection x, k * (1 - ‖x‖)) := by
  let A := (Diffeomorph.refl (𝓡 1) UnitCircle ∞).prodCongr (radiusToCollarTime k hk.ne')
  let P := circleRadialChart.symm.transHomeomorph A.toHomeomorph
  let C := (P.trans Q).trans e.symm
  have hP (x : E2) : P x = (circleDirection x, k * (1 - ‖x‖)) := rfl
  have hPm : ContMDiffOn 𝓘(ℝ, E2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ P P.source :=
    A.contMDiff_toFun.comp_contMDiffOn circleRadialChart_symm_contMDiffOn
  have hPi : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2) ∞ P.symm P.target :=
    circleRadialChart_contMDiffOn.comp A.contMDiff_invFun.contMDiffOn (fun _ hp => hp)
  have hCm : ContDiffOn ℝ ∞ C C.source :=
    (hei.comp (hQ.comp (hPm.mono (inter_subset_left.trans inter_subset_left))
      (fun _ hx => hx.1.2)) (fun _ hx => hx.2)).contDiffOn
  have hCi : ContDiffOn ℝ ∞ C.symm C.target :=
    (hPi.comp (hQi.comp (hem.mono inter_subset_left) (fun _ hx => hx.2.1))
      (fun _ hx => hx.2.2)).contDiffOn
  have hunit (x : E2) (hx : x ∈ sphere 0 1) :
      P x = (⟨x, hx⟩, 0) := by
    rw [hP, mem_sphere_zero_iff_norm.mp hx, sub_self, mul_zero]
    exact Prod.ext (circleDirection_coe_unit ⟨x, hx⟩) rfl
  have hCs : sphere (0 : E2) 1 ⊆ C.source := by
    intro x hx
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact ne_zero_of_mem_unit_sphere ⟨x, hx⟩
    · change P x ∈ Q.source
      rw [hunit x hx, hQs]
      exact ⟨mem_univ _, neg_neg_of_pos hd, hd⟩
    · change Q (P x) ∈ e.target
      rw [hunit x hx, ← hb ⟨x, hx⟩]
      exact e.map_source (he (sphere_subset_closedBall hx))
  have hfixed (x : E2) (hx : x ∈ sphere 0 1) : C x = x := by
    change e.symm (Q (P x)) = x
    rw [hunit x hx, ← hb ⟨x, hx⟩]
    exact e.left_inv (he (sphere_subset_closedBall hx))
  have hrec (x : E2) (hx : x ∈ C.source) :
      C x ∈ e.source ∧ e (C x) = Q (circleDirection x, k * (1 - ‖x‖)) := by
    refine ⟨e.map_target hx.2, ?_⟩
    change e (e.symm (Q (P x))) = _
    calc
      _ = Q (P x) := e.right_inv (show Q (P x) ∈ e.target from hx.2)
      _ = _ := congrArg Q (hP x)
  have hout (x : E2) (hx : x ∈ sphere 0 1) :
      ∀ᶠ y in 𝓝 x, 1 ≤ ‖y‖ → 1 ≤ ‖C y‖ := by
    filter_upwards [C.open_source.mem_nhds (hCs hx)] with y hy hnorm
    apply le_of_not_gt
    intro hyin
    have hyQ : P y ∈ Q.source := hy.1.2
    rw [hP, hQs] at hyQ
    apply hneg (circleDirection y) (k * (1 - ‖y‖)) hyQ.2
      (mul_nonpos_of_nonneg_of_nonpos hk.le (sub_nonpos.mpr hnorm))
    exact ⟨C y, mem_ball_zero_iff.mpr hyin, (hrec y hy).2⟩
  obtain ⟨F, hFfix, hFnear, hFball, hFclosed, _⟩ :=
    exists_oriented_collar_extension C hCm hCi hCs hfixed hout
  refine ⟨F, hFball, hFclosed, fun θ => hFfix θ.1 θ.2, ?_⟩
  have hCnear : ∀ᶠ x in 𝓝ˢ (sphere (0 : E2) 1), x ∈ C.source :=
    C.open_source.mem_nhdsSet.mpr hCs
  filter_upwards [hFnear, hCnear] with x hFx hx
  rw [hFx]
  exact hrec x hx




theorem exists_rectified_source_disc_chart
    (Q : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere)
    (hQ : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ Q Q.source)
    (hQi : ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ Q.symm Q.target)
    {d : ℝ} (hd : 0 < d) (hQs : Q.source = univ ×ˢ Ioo (-d) d)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : closedBall 0 1 ⊆ e.source)
    (hem : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target)
    (hb : ∀ θ : UnitCircle, e θ.1 = Q (θ, 0))
    (hneg : ∀ θ : UnitCircle, ∀ s ∈ Ioo (-d) d,
      s ≤ 0 → Q (θ, s) ∉ e '' ball 0 1)
    {k : ℝ} (hk : 0 < k) :
    ∃ f : OpenPartialHomeomorph E2 UnitTwoSphere,
      closedBall 0 1 ⊆ f.source ∧
      ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ f f.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ f.symm f.target ∧
      f '' ball 0 1 = e '' ball 0 1 ∧
      f '' closedBall 0 1 = e '' closedBall 0 1 ∧
      (∀ θ : UnitCircle, f θ.1 = Q (θ, 0)) ∧
      ∀ᶠ x in 𝓝ˢ (sphere (0 : E2) 1),
        x ∈ f.source ∧ f x = Q (circleDirection x, k * (1 - ‖x‖)) := by
  obtain ⟨F, hFball, hFclosed, hFfix, hFnear⟩ :=
    source_disc_collar_rectification Q hQ hQi hd hQs e he hem hei hb hneg hk
  let f := F.toHomeomorph.toOpenPartialHomeomorph.trans e
  have hfs : closedBall 0 1 ⊆ f.source := by
    intro x hx
    refine ⟨mem_univ _, he ?_⟩
    rw [← hFclosed]
    exact ⟨x, hx, rfl⟩
  refine ⟨f, hfs, hem.comp F.contMDiff_toFun.contMDiffOn (fun _ hx => hx.2),
    F.contMDiff_invFun.comp_contMDiffOn (hei.mono inter_subset_left), ?_, ?_, ?_, ?_⟩
  · change (fun x => e (F x)) '' ball 0 1 = _
    rw [← image_image e F, hFball]
  · change (fun x => e (F x)) '' closedBall 0 1 = _
    rw [← image_image e F, hFclosed]
  · intro θ
    change e (F θ.1) = _
    rw [hFfix θ, hb θ]
  · filter_upwards [hFnear] with x hx
    exact ⟨⟨mem_univ _, hx.1⟩, hx.2⟩

end PoincareConjecture.M25.Topology3D
