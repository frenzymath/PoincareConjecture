import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallBoundaryParametrization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarOrientation
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarRadialCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallCollarUnion

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem schoenfliesData_of_ball (ψ : UnitTwoSphere × ℝ → E3)
    (hψ : IsCollarEmbedding ψ) (B : BallNeighborhoodChart E3 E3)
    (hboundary : B.boundary = ψ '' (univ ×ˢ {0}))
    (δ : ℝ) (hδ : 0 < δ) (_hδ1 : δ < 1) : Nonempty (SchoenfliesData ψ δ) := by
  obtain ⟨side, hside, hinside, houtside⟩ := exists_ball_collar_orientation ψ hψ B hboundary
  obtain ⟨g, hg⟩ := exists_ball_boundary_parametrization ψ hψ B hboundary
  obtain ⟨R, hRs, hRf, hR, hRi, hRrad⟩ := exists_radial_collar_chart ψ hψ g hside
  have hRS : sphere (0 : E3) 1 ⊆ R.source := by
    intro x hx
    rw [hRs]
    have hn := mem_sphere_zero_iff_norm.mp hx
    exact ⟨by linarith, by linarith⟩
  have hRboundary (x : E3) (hx : x ∈ sphere (0 : E3) 1) : R x = B.chart x := by
    let q : UnitTwoSphere := ⟨x, hx⟩
    have h := hRrad (g.symm q) 0 (by norm_num) (by norm_num)
    simp only [add_zero, one_smul, g.apply_symm_apply, mul_zero] at h
    exact h.trans (by simpa only [g.apply_symm_apply] using (hg (g.symm q)).symm)
  have hRout (x : E3) (hx : x ∈ R.source) (hn : 1 < ‖x‖) : R x ∉ B.closedRegion := by
    have hx2 : ‖x‖ < 2 := (hRs ▸ hx).2
    exact houtside ⟨(g.symm (sphereDirection x), ‖x‖ - 1),
      ⟨mem_univ _, by constructor <;> linarith⟩, (hRf x).symm⟩
  obtain ⟨C, hCi, hCc, _hCb, hmatch⟩ :=
    exists_ball_chart_collar_match B R hR hRi hRS hRboundary hRout
  obtain ⟨J, hJs, hJ, hJi, hJim, hJrad⟩ :=
    exists_ball_outer_collar_union C R hRs hR hRi hmatch
      (fun x hx hn => by rw [hCc]; exact hRout x hx hn)
  have himage : R '' {x : E3 | 1 ≤ ‖x‖ ∧ ‖x‖ < 2} =
      (fun p : UnitTwoSphere × ℝ => ψ (p.1, side * p.2)) '' (univ ×ˢ Ico 0 1) := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact ⟨(g.symm (sphereDirection x), ‖x‖ - 1),
        ⟨mem_univ _, by constructor <;> linarith [hx.1, hx.2]⟩, (hRf x).symm⟩
    · rintro y ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
      have hr : 0 < 1 + s := by linarith [hs.1]
      refine ⟨(1 + s) • (g q : E3), ?_, hRrad q s (by linarith [hs.1]) hs.2⟩
      simp only [mem_ofPred_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
        norm_eq_of_mem_sphere, mul_one]
      constructor <;> linarith [hs.1, hs.2]
  have hJtarget : J '' ball 0 2 = J.target := by
    rw [← hJs]
    exact J.image_source_eq_target
  refine ⟨{
    side := side
    side_sq := hside
    inside := B.inside
    inside_open := B.inside_open
    inside_bounded := B.inside_bounded
    inside_connected := B.inside_connected
    inside_disjoint := hboundary ▸ B.inside_disjoint_boundary
    outside_connected := hboundary ▸ B.outside_connected
      (Module.one_lt_rank_of_one_lt_finrank (by simp [E3]))
    collar_inside := hinside
    radius := 2
    chart := J
    boundary_map := g
    radial := fun s => 1 + s
    chart_smooth := hJs ▸ hJ
    chart_injOn := hJs ▸ J.injOn
    chart_image := by rw [hJim, hCi, himage]
    chart_inverse := ⟨J.symm, hJtarget.symm ▸ hJi,
      fun x hx => J.left_inv (hJs.symm ▸ hx)⟩
    radial_strictMono := fun _ _ _ _ hab => by dsimp; linarith
    radial_pos := fun s hs => by linarith [hs.1, hδ]
    radial_lt := fun s hs => by linarith [hs.2]
    chart_collar := ?_ }⟩
  intro q s hs
  have hs0 : 0 ≤ s := le_trans hδ.le hs.1
  have hr : 0 < 1 + s := by linarith
  have hn : ‖(1 + s) • (g q : E3)‖ = 1 + s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
  rw [hJrad _ (by rw [hn]; linarith) (by rw [hn]; linarith [hs.2])]
  exact hRrad q s (by linarith) hs.2

end PoincareConjecture.M25.Topology3D
