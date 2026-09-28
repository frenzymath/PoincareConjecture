import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallCapSourceDisc
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallCapPlane
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryDiscCap
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallChartIsometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallChartReparametrization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallBoundaryParametrization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

attribute [local instance] sourceCircle_stereographic_dimension

theorem exists_sphere_disc_vertical_cap
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (hclosed : closedBall (0 : E2) 1 ⊆ e.source)
    (he : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target) :
    ∃ a : ℝ, a ∈ Ioo (1 / 2 : ℝ) 1 ∧
      ∃ G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
        (∀ y : E3, ‖G y‖ = ‖y‖) ∧
        G '' (((↑) : UnitTwoSphere → E3) ''
          (e '' closedBall (0 : E2) 1)) =
          {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2} := by
  obtain ⟨v, _hv, D, _hchart, _hDs, _hDt, _hD, _hDi, _hrec, himage⟩ :=
    exists_sphere_disc_plane_chart e hclosed he hei
  let U : (ℝ ∙ (v : E3))ᗮ ≃ₗᵢ[ℝ] E2 :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (ne_zero_of_mem_unit_sphere v)).repr
  let B := D.isometryConjugate U
  have hdim : 1 < Module.rank ℝ ((ℝ ∙ (v : E3))ᗮ) := by
    apply Module.one_lt_rank_of_one_lt_finrank
    rw [U.toLinearEquiv.finrank_eq]
    simp [E2]
  have hdim3 : 1 < Module.rank ℝ E3 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E3])
  have hsphere : IsPreconnected (sphere (0 : E3) 1) :=
    (isConnected_sphere hdim3 0 zero_le_one).isPreconnected
  obtain ⟨a, ha, F, hFnorm, hFimage, _C, _hC, _hfix⟩ :=
    exists_boundary_disc_cap (v : E3) (norm_eq_of_mem_sphere v) B hdim hsphere
  have hcoordinates : (fun w => (stereoInvFun (norm_eq_of_mem_sphere v) w : E3)) ''
      B.closedRegion =
      (fun x : E2 => ((stereographic' 2 v).symm (D.chart x) : E3)) ''
        closedBall (0 : E2) 1 := by
    ext y
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨U w, ?_, rfl⟩
      simpa only [mem_closedBall_zero_iff, U.norm_map] using hw
    · rintro ⟨x, hx, rfl⟩
      have hxU : U.symm x ∈ closedBall (0 : (ℝ ∙ (v : E3))ᗮ) 1 := by
        simpa only [mem_closedBall_zero_iff, U.symm.norm_map] using hx
      refine ⟨B.chart (U.symm x), ⟨U.symm x, hxU, rfl⟩, ?_⟩
      change (stereoInvFun (norm_eq_of_mem_sphere v)
          (U.symm (D.chart (U (U.symm x)))) : E3) =
        (stereoInvFun (norm_eq_of_mem_sphere v) (U.symm (D.chart x)) : E3)
      rw [U.apply_symm_apply]
  have hambient :
      (fun x : E2 => ((stereographic' 2 v).symm (D.chart x) : E3)) ''
        closedBall (0 : E2) 1 =
      ((↑) : UnitTwoSphere → E3) '' (e '' closedBall (0 : E2) 1) := by
    calc
      _ = ((↑) : UnitTwoSphere → E3) ''
          ((stereographic' 2 v).symm '' D.closedRegion) := by
        simp only [BallNeighborhoodChart.closedRegion, image_image]
      _ = _ := by rw [himage]
  rw [hcoordinates, hambient] at hFimage
  let R : E3 ≃ₗᵢ[ℝ] E3 :=
    (ℝ ∙ (-(v : E3) - EuclideanSpace.single (2 : Fin 3) 1))ᗮ.reflection
  have hRheight (y : E3) :
      (heightCoordinates (R y)).2 = ⟪-(v : E3), y⟫_ℝ :=
    heightPlaneCoordinates_snd (-v) y
  have hRimage : R '' {y : E3 | ‖y‖ = 1 ∧ a ≤ ⟪-(v : E3), y⟫_ℝ} =
      {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(R.norm_map x).trans hx.1, ?_⟩
      rw [hRheight]
      exact hx.2
    · intro hy
      refine ⟨R.symm y, ⟨?_, ?_⟩, R.apply_symm_apply y⟩
      · rw [R.symm.norm_map]
        exact hy.1
      · rw [← hRheight, R.apply_symm_apply]
        exact hy.2
  let G := F.trans R.toContinuousLinearEquiv.toDiffeomorph
  refine ⟨a, ha, G, ?_, ?_⟩
  · intro y
    change ‖R (F y)‖ = ‖y‖
    rw [R.norm_map, hFnorm]
  · change (fun y => R (F y)) ''
      (((↑) : UnitTwoSphere → E3) '' (e '' closedBall (0 : E2) 1)) = _
    rw [← image_image, hFimage, hRimage]

theorem exists_normalized_child_cap_ball
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u : UnitTwoSphere) (tag : SurgeryCapTag ψ u)
    (A0 : BallNeighborhoodChart E3 E3)
    (hboundary : A0.boundary = ψ '' (univ ×ˢ ({0} : Set ℝ))) :
    ∃ a : ℝ, a ∈ Ioo (1 / 2 : ℝ) 1 ∧
      ∃ G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      ∃ hG : (∀ y : E3, ‖G y‖ = ‖y‖),
        let A := A0.normReparametrize G hG
        A.chart = G.symm.toHomeomorph.toOpenPartialHomeomorph.trans A0.chart ∧
        A.chart.source = G.symm ⁻¹' A0.chart.source ∧
        A.chart.target = A0.chart.target ∧
        (∀ y : E3, A.chart y = A0.chart (G.symm y)) ∧
        (∀ Y : E3, A.chart.symm Y = G (A0.chart.symm Y)) ∧
        A.inside = A0.inside ∧
        A.closedRegion = A0.closedRegion ∧
        A.boundary = A0.boundary ∧
        A.chart '' {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2} =
          tag.cap := by
  obtain ⟨g, hg⟩ := exists_ball_boundary_parametrization ψ hψ A0 hboundary
  obtain ⟨e, _hes, _het, _heq, _heiq, hclosed, he, hei, hdisc⟩ :=
    exists_child_cap_source_disc ψ u tag g
  obtain ⟨a, ha, G, hG, hnormalize⟩ := exists_sphere_disc_vertical_cap e hclosed he hei
  have hcap : A0.chart '' (((↑) : UnitTwoSphere → E3) ''
      (e '' closedBall (0 : E2) 1)) = tag.cap := by
    change A0.chart '' (((↑) : UnitTwoSphere → E3) ''
      (e '' closedBall (0 : E2) 1)) =
        (fun q : UnitTwoSphere => ψ (q, 0)) '' tag.sourceCap
    rw [hdisc]
    simp only [image_image]
    apply image_congr
    intro q _hq
    exact hg q
  let A := A0.normReparametrize G hG
  have hAs : A.chart.source = G.symm ⁻¹' A0.chart.source := by
    ext y
    change (y ∈ (univ : Set E3) ∧ G.symm y ∈ A0.chart.source) ↔
      G.symm y ∈ A0.chart.source
    simp only [mem_univ, true_and]
  have hAt : A.chart.target = A0.chart.target := by
    ext Y
    change (Y ∈ A0.chart.target ∧ A0.chart.symm Y ∈ (univ : Set E3)) ↔
      Y ∈ A0.chart.target
    simp only [mem_univ, and_true]
  refine ⟨a, ha, G, hG, rfl, hAs, hAt, fun _ => rfl, fun _ => rfl,
    A0.normReparametrize_inside G hG, A0.normReparametrize_closedRegion G hG,
    A0.normReparametrize_boundary G hG, ?_⟩
  rw [← hnormalize, image_image]
  simpa only [A, BallNeighborhoodChart.normReparametrize_apply,
    G.symm_apply_apply] using hcap

end PoincareConjecture.M25.Topology3D
