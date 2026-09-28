import PoincareConjecture.Proofs.M38.BallNormalCorrection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.MatchingBoundary











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)



noncomputable def exponentialLinearCollar :
    PartialDiffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞ where
  toFun z := (z.1, Real.exp z.2 - 1)
  invFun z := (z.1, Real.log (1 + z.2))
  source := univ
  target := univ ×ˢ Ioi (-1 : ℝ)
  map_source' := by
    intro z _
    refine ⟨mem_univ _, ?_⟩
    change (-1 : ℝ) < Real.exp z.2 - 1
    linarith [Real.exp_pos z.2]
  map_target' := fun _ _ => mem_univ _
  left_inv' := by
    intro z _
    apply Prod.ext
    · rfl
    change Real.log (1 + (Real.exp z.2 - 1)) = z.2
    rw [show 1 + (Real.exp z.2 - 1) = Real.exp z.2 by ring, Real.log_exp]
  right_inv' := by
    intro z hz
    apply Prod.ext
    · rfl
    change Real.exp (Real.log (1 + z.2)) - 1 = z.2
    have hz' : (-1 : ℝ) < z.2 := hz.2
    rw [Real.exp_log (by linarith)]
    ring
  open_source := isOpen_univ
  open_target := isOpen_univ.prod isOpen_Ioi
  contMDiffOn_toFun :=
    (contMDiff_fst.prodMk
      ((Real.contDiff_exp.contMDiff.comp contMDiff_snd).sub contMDiff_const)).contMDiffOn
  contMDiffOn_invFun := by
    intro z hz
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_fst.prodMk
    have hz' : (-1 : ℝ) < z.2 := hz.2
    exact (Real.contDiffAt_log.mpr (by linarith)).contMDiffAt.comp z
      (contMDiff_const.add contMDiff_snd).contMDiffAt



theorem exists_ballNeighborhood_matching_linear_collar
    {A : GeneralizedSliceCarrier.{u}}
    (b : OpenPartialHomeomorph StandardCapSpace A.carrier)
    (hbs : Metric.closedBall 0 1 ⊆ b.source)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    (c : PartialDiffeomorph CylModel (𝓡 3) RoundCylinderSpace A.carrier ∞)
    {δ : ℝ} (hδ : 0 < δ)
    (hsource : univ ×ˢ Ioo (-δ) δ ⊆ c.source)
    (hzero : c '' (univ ×ˢ ({0} : Set ℝ)) = b '' Metric.sphere 0 1)
    (hpositive : ∀ (q : UnitTwoSphere) (t : ℝ), 0 < t → t < δ →
      c (q, t) ∉ b '' Metric.closedBall 0 1) :
    ∃ (r : ℝ) (a : OpenPartialHomeomorph StandardCapSpace A.carrier),
      0 < r ∧ r < 1 / 2 ∧ Metric.closedBall 0 1 ⊆ a.source ∧
      a.target = b.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ a a.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ a.symm a.target ∧
      a '' Metric.closedBall 0 1 = b '' Metric.closedBall 0 1 ∧
      ∀ (z : UnitTwoSphere) (s : ℝ), |s| < r →
        (1 + s) • z.val ∈ a.source ∧ a ((1 + s) • z.val) = c (z, s) := by
  have hcont : Continuous (fun t : ℝ => Real.exp t - 1) :=
    Real.continuous_exp.sub continuous_const
  have hneigh : (fun t : ℝ => Real.exp t - 1) ⁻¹' Ioo (-δ) δ ∈ 𝓝 0 :=
    hcont.continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds (by simpa using (show -δ < 0 ∧ 0 < δ from
        ⟨neg_lt_zero.mpr hδ, hδ⟩)))
  obtain ⟨γ, hγ, hγsub⟩ := Metric.mem_nhds_iff.mp hneigh
  let d := exponentialLinearCollar.trans c
  have hdsource : univ ×ˢ Ioo (-γ) γ ⊆ d.source := by
    intro z hz
    refine ⟨mem_univ _, hsource ?_⟩
    have hzball : z.2 ∈ Metric.ball (0 : ℝ) γ := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using (abs_lt.mpr hz.2)
    exact ⟨mem_univ _, hγsub hzball⟩
  have hd_zero (z : UnitTwoSphere) : d (z, 0) = c (z, 0) := by
    change c (z, Real.exp 0 - 1) = c (z, 0)
    rw [Real.exp_zero, sub_self]
  have hdzero : d '' (univ ×ˢ ({0} : Set ℝ)) = b '' Metric.sphere 0 1 := by
    rw [← hzero]
    apply image_congr
    rintro ⟨z, s⟩ ⟨_, hs⟩
    have hs0 : s = 0 := hs
    subst s
    exact hd_zero z
  have hdpositive (z : UnitTwoSphere) (t : ℝ) (ht : 0 < t) (htγ : t < γ) :
      d (z, t) ∉ b '' Metric.closedBall 0 1 := by
    apply hpositive
    · have hexp : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
      linarith
    · have htball : t ∈ Metric.ball (0 : ℝ) γ := by
        simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htγ
      exact (hγsub htball).2
  obtain ⟨η, a, hη, _, has, hat, ha, hai, hab, hmatch⟩ :=
    Poincare.exists_ball_neighborhood_matching_boundary_collar b hbs hb hbi
      d.toOpenPartialHomeomorph d.contMDiffOn_toFun d.contMDiffOn_invFun
      hγ hdsource hdzero hdpositive
  have hlog : ContinuousAt (fun s : ℝ => Real.log (1 + s)) 0 :=
    (Real.continuousAt_log (by norm_num : (1 + (0 : ℝ)) ≠ 0)).comp
      (continuous_const.add continuous_id).continuousAt
  have hlogneigh : {s : ℝ | |Real.log (1 + s)| < η} ∈ 𝓝 0 :=
    hlog.abs.preimage_mem_nhds (isOpen_Iio.mem_nhds (by simpa using hη))
  obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.mem_nhds_iff.mp hlogneigh
  let r := min r₀ (1 / 4)
  have hr : 0 < r := lt_min hr₀ (by norm_num)
  refine ⟨r, a, hr, (min_le_right _ _).trans_lt (by norm_num), has, hat,
    ha, hai, hab, ?_⟩
  intro z s hs
  have hsquarter : |s| < 1 / 4 := hs.trans_le (min_le_right _ _)
  have hspos : 0 < 1 + s := by linarith [neg_le_abs s]
  have hsball : s ∈ Metric.ball (0 : ℝ) r₀ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
      (hs.trans_le (min_le_left _ _))
  have hslog : |Real.log (1 + s)| < η := hr₀sub hsball
  have h := hmatch (z, Real.log (1 + s)) hslog
  change Real.exp (Real.log (1 + s)) • z.val ∈ a.source ∧
    a (Real.exp (Real.log (1 + s)) • z.val) = d (z, Real.log (1 + s)) at h
  have he : Real.exp (Real.log (1 + s)) = 1 + s := Real.exp_log hspos
  refine ⟨by simpa only [he] using h.1, ?_⟩
  calc
    a ((1 + s) • z.val) = d (z, Real.log (1 + s)) := by
      simpa only [he] using h.2
    _ = c (z, s) := by
      change c (z, Real.exp (Real.log (1 + s)) - 1) = c (z, s)
      rw [he]
      congr 2
      ring




theorem exists_surgeryBall_matching_linear_collar
    {A : GeneralizedSliceCarrier.{u}}
    (b : OpenPartialHomeomorph StandardCapSpace A.carrier)
    (hbs : Metric.closedBall 0 1 ⊆ b.source)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    (c : OpenPartialHomeomorph RoundCylinderSpace A.carrier)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ)
    (hsource : univ ×ˢ Ioo (-δ) δ ⊆ c.source)
    (hzero : c '' (univ ×ˢ ({0} : Set ℝ)) = b '' Metric.sphere 0 1)
    (hpositive : ∀ (q : UnitTwoSphere) (t : ℝ), 0 < t → t < δ →
      c (q, t) ∉ b '' Metric.closedBall 0 1) :
    ∃ (r : ℝ) (D : SurgeryBallEmbedding A),
      0 < r ∧ r < 1 / 2 ∧ D.closedBall = b '' Metric.closedBall 0 1 ∧
      D.map '' Metric.ball 0 2 ⊆ b.target ∧
      ∀ (z : UnitTwoSphere) (s : ℝ), |s| < r →
        D.map ((1 + s) • z.val) = c (z, s) := by
  let j : PartialDiffeomorph CylModel (𝓡 3) RoundCylinderSpace A.carrier ∞ := {
    toPartialEquiv := c.toPartialEquiv
    open_source := c.open_source
    open_target := c.open_target
    contMDiffOn_toFun := hc
    contMDiffOn_invFun := hci }
  obtain ⟨r, a, hr, hrhalf, has, hat, ha, hai, hab, hmatch⟩ :=
    exists_ballNeighborhood_matching_linear_collar b hbs hb hbi j
      hδ hsource hzero hpositive
  obtain ⟨s, D, hs, _, hD, hDt, hradial⟩ :=
    exists_surgeryBall_preserving_radial_germ a ha hai has
  refine ⟨min r s, D, lt_min hr hs, (min_le_left _ _).trans_lt hrhalf,
    hD.trans hab, hat ▸ hDt, ?_⟩
  intro z t ht
  rw [hradial z t (ht.trans_le (min_le_right _ _))]
  exact (hmatch z t (ht.trans_le (min_le_left _ _))).2

end PoincareConjecture.M38
