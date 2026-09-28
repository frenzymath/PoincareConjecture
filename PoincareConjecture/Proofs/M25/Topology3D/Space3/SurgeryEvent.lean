import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularDiscSurgery











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


structure RegularSurgeryEvent
    (parent : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere) where
  parent_embedding : IsCollarEmbedding parent
  cutHeight : ℝ
  data : RegularSurgeryData parent u cutHeight
  profile : SurgeryCapProfile
  radius : ℝ
  radius_mem : radius ∈ Ioo (0 : ℝ) 1
  radialWidth : ℝ
  radius_near : 1 - radius < radialWidth
  radial : ∀ (i : Fin 2) (x : E2), |‖x‖ - 1| < radialWidth →
    x ∈ (![data.sourceDiscs.positive, data.sourceDiscs.negative] i).source ∧
      (![data.sourceDiscs.positive, data.sourceDiscs.negative] i) x =
        data.sourceCollar (circleDirection x,
          (![1, -1] i) * (data.width / 2 * (1 - ‖x‖)))
  scale : ℝ
  matching : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞
  matching_closedBall : matching '' closedBall (0 : E2) 1 = closedBall 0 radius
  matching_circle : ∀ x ∈ sphere (0 : E2) 1, matching x = radius • x
  child : Fin 2 → UnitTwoSphere × ℝ → E3
  child_embedding : ∀ i, IsCollarEmbedding (child i)
  child_central : ∀ i (q : UnitTwoSphere), child i (q, 0) =
    profile.replacementMap parent matching
      (![data.sourceDiscs.positive, data.sourceDiscs.negative] i)
      data.tube cutHeight (![1, -1] i) radius (data.width / 2) scale q
  newCap : (i : Fin 2) → SurgeryCapTag (child i) u
  newCap_spec : ∀ i, (newCap i).profile = profile ∧
    (newCap i).tube = data.tube ∧ (newCap i).cutHeight = cutHeight ∧
    (newCap i).removal = data.width / 2 * (1 - radius) ∧
    (newCap i).scale = scale ∧ (newCap i).sign = (![1, -1] i)
  retainedChart : Fin 2 → OpenPartialHomeomorph UnitTwoSphere UnitTwoSphere
  retainedTime : Fin 2 → ℝ
  retained_spec : ∀ i,
    let e := (![data.sourceDiscs.positive, data.sourceDiscs.negative] i)
    let ret := retainedChart i
    retainedTime i ≠ 0 ∧ |retainedTime i| < 1 ∧
    ret.source ⊆ (surgeryNorthChart matching e).source ∧
    ret.target ⊆ (surgeryNorthChart matching e).target ∧
    (∀ p, ret p = surgeryNorthChart matching e p) ∧
    (∀ p, ret.symm p = (surgeryNorthChart matching e).symm p) ∧
    {p : UnitTwoSphere | 0 ≤ (heightCoordinates (p : E3)).2} ⊆ ret.source ∧
    e '' closedBall (0 : E2) radius ⊆ ret.target ∧
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ ret ret.source ∧
    ContMDiffOn (𝓡 2) (𝓡 2) ∞ ret.symm ret.target ∧
    ∀ p ∈ ret.source, ∀ s : ℝ, |s| < 1 →
      child i (p, s) = parent (ret p, retainedTime i * s)


theorem exists_regular_surgery_event (P : SurgeryCapProfile)
    (parent : UnitTwoSphere × ℝ → E3) (hparent : IsCollarEmbedding parent)
    (u : UnitTwoSphere) (t : ℝ) (D : RegularSurgeryData parent u t) :
    ∃ E : RegularSurgeryEvent parent u,
      E.cutHeight = t ∧ HEq E.data D ∧ E.profile = P := by
  classical
  obtain ⟨delta, r, l, R, child, _hd, hr, hr1, hrd, _hc, _hcw, _hl, _hlM,
    _hRo, hRc, hRs, _hRn, hnear, hchildren, _hdisjoint⟩ :=
    exists_regular_disc_surgery P parent hparent u t D
  choose ret gamma C hgamma hgammaSmall _hbeta hsrc htar hret hreti hretK
    htarget hsm hsi heq hprofile htube hcut hremoval hscale hsign
    _hidentity _hflat _hwidth _hsourceCap _hcap _hseam using
      fun i : Fin 2 => (hchildren i).2.2.2
  let E : RegularSurgeryEvent parent u := {
    parent_embedding := hparent
    cutHeight := t
    data := D
    profile := P
    radius := r
    radius_mem := ⟨hr, hr1⟩
    radialWidth := delta
    radius_near := hrd
    radial := hnear
    scale := l
    matching := R
    matching_closedBall := hRc
    matching_circle := hRs
    child := child
    child_embedding := fun i => (hchildren i).1
    child_central := fun i => (hchildren i).2.1
    newCap := C
    newCap_spec := fun i =>
      ⟨hprofile i, htube i, hcut i, hremoval i, hscale i, hsign i⟩
    retainedChart := ret
    retainedTime := gamma
    retained_spec := fun i =>
      ⟨hgamma i, hgammaSmall i, hsrc i, htar i, hret i, hreti i,
        hretK i, htarget i, hsm i, hsi i, heq i⟩ }
  exact ⟨E, rfl, HEq.rfl, rfl⟩


theorem RegularSurgeryEvent.parameter_bounds
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u) :
    let c := E.data.width / 2 * (1 - E.radius)
    0 < E.radialWidth ∧ 0 < c ∧ c < E.data.width / 2 ∧
      E.data.width / 2 < E.data.width ∧ 0 < E.scale ∧
      E.scale * E.profile.heightBound < c / 4 := by
  have hk : 0 < E.data.width / 2 := by linarith [E.data.width_pos]
  obtain ⟨hprofile, _htube, _hcut, hremoval, hscale, _hsign⟩ := E.newCap_spec 0
  have hl := (E.newCap 0).scale_pos
  have hlM := (E.newCap 0).scale_small
  rw [hscale] at hl
  rw [hscale, hprofile, hremoval] at hlM
  refine ⟨?_, mul_pos hk (by linarith [E.radius_mem.2]), ?_, ?_, hl, hlM⟩
  · linarith [E.radius_mem.2, E.radius_near]
  · nlinarith [mul_pos hk E.radius_mem.1]
  · linarith [E.data.width_pos]

end PoincareConjecture.M25.Topology3D
