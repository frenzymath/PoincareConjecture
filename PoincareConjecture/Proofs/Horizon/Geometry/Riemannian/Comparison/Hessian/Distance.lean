import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Inverse
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Tail
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Support











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem exists_distance_hessian_upper_support
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ y : M, ∀ u v : TangentSpace (𝓡 n) y,
      -K ≤ D.sectionalCurvature y u v)
    (p x : M) (hpx : p ≠ x) :
    ∃ (U : Set M) (rho : M → ℝ), IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U ∧
      rho x = (g.edist p x).toReal ∧
      (∀ y ∈ U, (g.edist p y).toReal ≤ rho y) ∧
      g.inner x (D.gradient rho x) (D.gradient rho x) = 1 ∧
      ∀ w : TangentSpace (𝓡 n) x,
        D.hessian rho x w w ≤
          (4 / (3 * (g.edist p x).toReal) + K * (g.edist p x).toReal / 4) *
            g.inner x w w := by
  obtain ⟨ε, γ, R, L, e, v, B, hε, hγ, hγ0, hγ1, hγmin, hR, hdR,
      hL, hnorm, he, he0, hed, hradial, hv, hv0, hx, hvnorm, hsplit,
      hleft, hmin, hi, hvB, hBU, heB, hB, hBi, hzero, hnormB, hmajor⟩ :=
    g.exists_smooth_radial_inverse_branch_of_shift D hcomplete p x hpx
      (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
  have hxB : B v = x := (heB hvB).symm.trans hx
  have hxmem : x ∈ B.target := hxB ▸ B.map_source hvB
  have hradx := hnormB.contMDiffAt (B.open_target.mem_nhds hxmem)
  have hnormx : ‖B.symm x‖ = (1 - 1 / 4) * (g.edist p x).toReal := by
    rw [show B.symm x = v by rw [← hxB, B.left_inv hvB]]
    exact hvnorm
  refine ⟨B.target, (fun y => (1 / 4) * (g.edist p x).toReal + ‖B.symm y‖),
    B.open_target, hxmem, contMDiffOn_const.add hnormB, ?_, hmajor, ?_, ?_⟩
  · dsimp only
    rw [hnormx]
    ring
  · rw [D.gradient_const_add_at (hradx.mdifferentiableAt (by simp))]
    have h := g.inner_gradient_inverse_branch D B heB hB hBi hvB hv0
      (g.radial_gauss_identity D he hnorm (fun w hw => (hradial w hw).1) v hv)
    rw [hx] at h
    exact h
  · intro w
    rw [D.hessian_const_add_at hradx]
    have h := g.hessian_inverse_radius_le_of_sectional_lower_bound D hK hsec he hnorm
      (fun z hz => (hradial z hz).1) B heB hB hBi hv hvB hv0 hmin
      (show TangentSpace (𝓡 n) (e v) from w)
    rw [hx, hvnorm] at h
    convert h using 1
    ring

end PoincareConjecture.RiemannianMetric
