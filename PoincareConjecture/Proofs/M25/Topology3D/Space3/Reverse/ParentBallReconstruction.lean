import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallEventCompression
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallEventReunion
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallBoundaryParametrization

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem RegularSurgeryEvent.exists_parent_ball_of_children
    {parent : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (E : RegularSurgeryEvent parent u)
    (A : Fin 2 → BallNeighborhoodChart E3 E3)
    (hboundary : ∀ k : Fin 2,
      (A k).boundary = E.child k '' (univ ×ˢ ({0} : Set ℝ))) :
    ∃ B : BallNeighborhoodChart E3 E3,
      B.boundary = parent '' (univ ×ˢ ({0} : Set ℝ)) ∧
      ∃ i : Fin 2,
        ∃ H R : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
          R '' (A i).boundary = H '' (parent '' (univ ×ˢ ({0} : Set ℝ))) ∧
          B.chart = (A i).chart.trans
            (R.trans H.symm).toHomeomorph.toOpenPartialHomeomorph ∧
          B.chart.source = (A i).chart.source ∧
          B.chart.target = H.symm '' (R '' (A i).chart.target) ∧
          (∀ x : E3, B.chart x = H.symm (R ((A i).chart x))) ∧
          (∀ Y : E3, B.chart.symm Y = (A i).chart.symm (R.symm (H Y))) ∧
          B.inside = H.symm '' (R '' (A i).inside) ∧
          B.closedRegion = H.symm '' (R '' (A i).closedRegion) ∧
          ∃ g : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞,
            ∀ q : UnitTwoSphere, B.chart (g q : E3) = parent (q, 0) := by
  obtain ⟨i, _hregions, Ω, _hΩ, _hΩdis, _hΩnest, H, S, _hS, _hSΩ,
      _hs, _his, _hHi, _hHcl, _hHb, _hprotected, _hstationaryInside,
      _hstationaryClosed, _hstationaryBoundary, _hstationaryPoint,
      _hSnest, _hcoreImage, hparentImage, _hparameters⟩ :=
    E.exists_supported_child_compression A hboundary
  obtain ⟨R, C, _hC, _hCwhere, _hsR, _hisR, _hRfix, _hRcap, _hRcapInv,
      hRsurface, _hRsurfaceInv⟩ := E.exists_event_reunion_diffeomorph i
  have hother : (![1, -1] (![1, 0] i) : ℝ) = -(![1, -1] i) := by
    fin_cases i <;> norm_num
  have hRH : R '' (A i).boundary = H '' (parent '' (univ ×ˢ ({0} : Set ℝ))) := by
    rw [hboundary i, hRsurface, hparentImage, hother]
  let K := R.trans H.symm
  let B : BallNeighborhoodChart E3 E3 := {
    chart := (A i).chart.trans K.toHomeomorph.toOpenPartialHomeomorph
    closedBall_subset_source := fun x hx =>
      ⟨(A i).closedBall_subset_source hx, mem_univ _⟩
    smooth := K.contMDiff_toFun.contDiff.comp_contDiffOn
      ((A i).smooth.mono (fun _ hx => hx.1))
    smooth_symm := (A i).smooth_symm.comp K.contMDiff_invFun.contDiff.contDiffOn
      (fun _ hy => hy.2) }
  have hBs : B.chart.source = (A i).chart.source := by
    ext x
    change (x ∈ (A i).chart.source ∧ (A i).chart x ∈ (univ : Set E3)) ↔
      x ∈ (A i).chart.source
    simp only [mem_univ, and_true]
  have hBt : B.chart.target = H.symm '' (R '' (A i).chart.target) := by
    ext y
    change (y ∈ (univ : Set E3) ∧ K.symm y ∈ (A i).chart.target) ↔
      y ∈ H.symm '' (R '' (A i).chart.target)
    constructor
    · intro hy
      exact ⟨R (K.symm y), ⟨K.symm y, hy.2, rfl⟩, K.apply_symm_apply y⟩
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨mem_univ _, ?_⟩
      change R.symm (H (H.symm (R x))) ∈ (A i).chart.target
      simpa only [H.apply_symm_apply, R.symm_apply_apply] using hx
  have himage (D : Set E3) :
      B.chart '' D = H.symm '' (R '' ((A i).chart '' D)) := by
    simp only [image_image]
    rfl
  have hBb : B.boundary = parent '' (univ ×ˢ ({0} : Set ℝ)) := by
    change B.chart '' sphere (0 : E3) 1 = _
    rw [himage]
    change H.symm '' (R '' (A i).boundary) = _
    rw [hRH, image_image]
    simpa only [H.symm_apply_apply] using
      (image_id' (parent '' (univ ×ˢ ({0} : Set ℝ))))
  obtain ⟨g, hg⟩ := exists_ball_boundary_parametrization parent E.parent_embedding B hBb
  exact ⟨B, hBb, i, H, R, hRH, rfl, hBs, hBt, fun _ => rfl, fun _ => rfl,
    himage (ball (0 : E3) 1), himage (closedBall (0 : E3) 1), g, hg⟩

end PoincareConjecture.M25.Topology3D
