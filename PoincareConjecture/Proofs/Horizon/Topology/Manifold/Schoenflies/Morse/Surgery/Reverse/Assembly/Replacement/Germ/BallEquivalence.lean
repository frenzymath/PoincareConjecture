import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Germ.Stationary
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Germ.BallBoundary
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Germ.DiskNeighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.RadialBody

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem exists_ball_equivalence_fixing_disk_neighborhood
    (B D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hnest : D '' (B '' closedBall (0 : E3) 1) ⊆ B '' closedBall (0 : E3) 1)
    (g : E2 -> E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgd : ∀ x, Injective (fderiv Real g x))
    {r : Real} (hr : 1 < r)
    (hsub : g '' closedBall (0 : E2) r ⊆ B '' sphere (0 : E3) 1)
    (hfix : ∀ x ∈ g '' closedBall (0 : E2) r, D x = x) :
    ∃ E : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      ∃ W : Set E3, IsOpen W ∧ g '' closedBall (0 : E2) 1 ⊆ W ∧
        (∀ x ∈ W, E x = x) ∧
        E '' (B '' closedBall (0 : E3) 1) = D '' (B '' closedBall (0 : E3) 1) := by
  obtain ⟨ρ, hρ, hρr⟩ := exists_between hr
  have hρpos : 0 < ρ := zero_lt_one.trans hρ
  have hrpos : 0 < r := zero_lt_one.trans hr
  let P : Set E3 := g '' closedBall (0 : E2) ρ
  let K : Set E3 := g '' closedBall (0 : E2) 1
  have hP : IsCompact P := (isCompact_closedBall _ _).image hg.continuous
  have hK : IsCompact K := (isCompact_closedBall _ _).image hg.continuous
  have hKP : K ⊆ P := image_mono (closedBall_subset_closedBall hρ.le)
  have hPr : P ⊆ g '' closedBall (0 : E2) r :=
    image_mono (closedBall_subset_closedBall hρr.le)
  have hPsphere : P ⊆ B '' sphere (0 : E3) 1 := hPr.trans hsub
  obtain ⟨U, hU, hKU, hUboundary⟩ :=
    exists_open_boundary_patch_for_disk B g hg hgi hgd hρpos hρ hPsphere
  obtain ⟨T, hT, hPT, hTboundary⟩ :=
    exists_open_boundary_patch_for_disk B g hg hgi hgd hrpos hρr hsub
  have hDfix : ∀ x ∈ P, D x = x := fun x hx => hfix x (hPr hx)
  have hder (t : Real) (ht : t ∈ Icc (0 : Real) 1) (x : E3) (hx : x ∈ P) :
      Function.Bijective (fderiv Real (fun y => (1 - t) • y + t • D y) x) :=
    bijective_fderiv_homotopy_of_ambient_ball_boundary B D hnest hT
      (fun y hy => hfix y (hTboundary hy)) ⟨hPT hx, hPsphere hx⟩ ht
  obtain ⟨S, _, _, V, hV, hKV, F, _, hFD, hFsphere⟩ :=
    exists_supported_germ_of_stationary D.contMDiff.contDiff hP hK hKP hDfix
      hder hU hKU hUboundary
  have hFboundary : F '' (B '' sphere (0 : E3) 1) = B '' sphere (0 : E3) 1 := by
    calc
      F '' (B '' sphere (0 : E3) 1) = id '' (B '' sphere (0 : E3) 1) :=
        image_congr hFsphere
      _ = B '' sphere (0 : E3) 1 := image_id _
  have hdim : 1 < Module.rank Real E3 := by rw [← Module.finrank_eq_rank]; norm_num
  have hBFboundary : (B.trans F).toHomeomorph '' sphere (0 : E3) 1 =
      B.toHomeomorph '' sphere (0 : E3) 1 := by
    change (F ∘ B) '' sphere (0 : E3) 1 = B '' sphere (0 : E3) 1
    rw [image_comp, hFboundary]
  have hFbody : F '' (B '' closedBall (0 : E3) 1) = B '' closedBall (0 : E3) 1 := by
    have h := (B.trans F).toHomeomorph.image_closedBall_eq_of_image_sphere_eq
      B.toHomeomorph hdim hBFboundary
    change (F ∘ B) '' closedBall (0 : E3) 1 = B '' closedBall (0 : E3) 1 at h
    rwa [image_comp] at h
  have hFsymmBody : F.symm '' (B '' closedBall (0 : E3) 1) = B '' closedBall (0 : E3) 1 := by
    calc
      F.symm '' (B '' closedBall (0 : E3) 1) =
          F.symm '' (F '' (B '' closedBall (0 : E3) 1)) := congrArg (image F.symm) hFbody.symm
      _ = B '' closedBall (0 : E3) 1 := by
        rw [← image_comp]
        simp only [Function.comp_def, F.symm_apply_apply, image_id']
  refine ⟨F.symm.trans D, F '' V, F.toHomeomorph.isOpenMap V hV, ?_, ?_, ?_⟩
  · intro x hx
    have hxV : x ∈ V := hKV hx
    refine ⟨x, hxV, ?_⟩
    exact (hFD hxV).trans (hDfix x (hKP hx))
  · rintro _ ⟨x, hx, rfl⟩
    change D (F.symm (F x)) = F x
    rw [F.symm_apply_apply]
    exact (hFD hx).symm
  · change (D ∘ F.symm) '' (B '' closedBall (0 : E3) 1) = _
    rw [image_comp, hFsymmBody]

end Poincare.Manifold.Schoenflies.Reverse
