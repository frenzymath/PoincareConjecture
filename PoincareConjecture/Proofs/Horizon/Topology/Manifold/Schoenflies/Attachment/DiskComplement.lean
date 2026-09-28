import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.MarkedBall
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Hemisphere.Caps












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

private theorem exists_sphere_restriction
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hball : F '' closedBall 0 1 = closedBall 0 1) :
    ∃ d : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞, ∀ p : S2, (d p : E3) = F p := by
  have hs : F '' sphere (0 : E3) 1 = sphere 0 1 := by
    have h := F.toHomeomorph.image_frontier (closedBall (0 : E3) 1)
    change F '' frontier (closedBall 0 1) = frontier (F '' closedBall 0 1) at h
    simpa only [hball, frontier_closedBall _ (by norm_num : (1 : Real) ≠ 0)] using h
  have hi (p : S2) : F.symm p ∈ sphere (0 : E3) 1 := by
    obtain ⟨x, hx, heq⟩ := hs.superset p.property
    rwa [← heq, F.symm_apply_apply]
  let e : S2 ≃ S2 := {
    toFun := fun p => ⟨F p, hs.subset (mem_image_of_mem F p.property)⟩
    invFun := fun p => ⟨F.symm p, hi p⟩
    left_inv := fun p => Subtype.ext (F.symm_apply_apply p)
    right_inv := fun p => Subtype.ext (F.apply_symm_apply p) }
  exact ⟨{
    toEquiv := e
    contMDiff_toFun := (F.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere _
    contMDiff_invFun := (F.symm.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere _ },
    fun _ => rfl⟩



theorem exists_complementary_disk_neighborhood
    {r : Real} (hr : 0 < r) (f : E2 -> S2)
    (hinj : InjOn f (closedBall 0 r))
    (hloc : ∀ x ∈ closedBall (0 : E2) r,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ f x) :
    ∃ (R : Real) (e : OpenPartialHomeomorph E2 S2),
      0 < R ∧ closedBall 0 R ⊆ e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      e '' closedBall 0 R = (f '' ball 0 r)ᶜ := by
  obtain ⟨J, F, hFball, hF⟩ := exists_marked_disk_round_coordinates hr f hinj hloc
  obtain ⟨d, hd⟩ := exists_sphere_restriction F hFball
  let v : E3 := f 0
  have hv : ‖v‖ = 1 := norm_eq_of_mem_sphere (f 0)
  have hdf (x : E2) (hx : x ∈ closedBall 0 r) :
      d (f x) = Hemisphere.toSphere hv (J x) := by
    apply Subtype.ext
    exact (hd (f x)).trans (hF x hx)
  have hJball (s : Real) : J '' ball (0 : E2) s = ball 0 s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_ball_zero_iff, J.norm_map] using hy
    · intro hx
      exact ⟨J.symm x, by simpa only [mem_ball_zero_iff, J.symm.norm_map] using hx,
        J.apply_symm_apply x⟩
  have hJclosed (s : Real) : J '' closedBall (0 : E2) s = closedBall 0 s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_closedBall, dist_zero_right, J.norm_map] using hy
    · intro hx
      exact ⟨J.symm x, by simpa only [mem_closedBall, dist_zero_right, J.symm.norm_map] using hx,
        J.apply_symm_apply x⟩
  have himage : d '' (f '' ball 0 r) =
      Hemisphere.toSphere hv '' ball (0 : Hemisphere.Plane v) r := by
    rw [image_image]
    calc
      (fun x => d (f x)) '' ball 0 r =
          (fun x => Hemisphere.toSphere hv (J x)) '' ball 0 r :=
        image_congr (fun x hx => hdf x (ball_subset_closedBall hx))
      _ = Hemisphere.toSphere hv '' ball 0 r := by rw [← image_image, hJball]
  let R := Hemisphere.complementRadius (Hemisphere.capHeight r)
  let e := (J.toHomeomorph.toOpenPartialHomeomorph.trans (stereographic hv).symm).trans
    d.symm.toHomeomorph.toOpenPartialHomeomorph
  have he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source :=
    d.symm.contMDiff.comp_contMDiffOn
      ((Hemisphere.contMDiff_stereoInvFun hv).comp
        J.toContinuousLinearEquiv.contDiff.contMDiff).contMDiffOn
  have hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target := by
    apply J.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp_contMDiffOn
    apply (Hemisphere.contMDiffOn_stereographic hv).comp d.contMDiff.contMDiffOn
    intro p hp
    exact hp.2.1
  refine ⟨R, e, Hemisphere.complementRadius_pos
    (by linarith [Hemisphere.capHeight_pos r]) (Hemisphere.capHeight_lt_one hr),
    (fun _ _ => ⟨⟨mem_univ _, mem_univ _⟩, mem_univ _⟩), he, hei, ?_⟩
  change (fun x => d.symm (stereoInvFun hv (J x))) '' closedBall 0 R = _
  calc
    (fun x => d.symm (stereoInvFun hv (J x))) '' closedBall 0 R =
        d.symm '' (stereoInvFun hv '' (J '' closedBall 0 R)) := by
      rw [image_image, image_image]
    _ = (f '' ball 0 r)ᶜ := by
      rw [hJclosed, ← Hemisphere.complement_image_ball_toSphere hv hr, ← himage]
      change d.toEquiv.symm '' (d.toEquiv '' (f '' ball 0 r))ᶜ = _
      rw [← d.toEquiv.image_compl, d.toEquiv.symm_image_image]

end Poincare.Manifold.Schoenflies
