import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Inverse








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem gradient_const_add_at (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) f x) (c : ℝ) :
    D.gradient (fun y => c + f y) x = D.gradient f x := by
  apply (g.inner_isInvertible x).injective
  ext v
  simp only [D.inner_gradient, mvfderiv_fun_add mdifferentiableAt_const hf,
    mvfderiv_const, zero_add]

theorem laplacian_const_add_at (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x) (c : ℝ) :
    D.laplacian (fun y => c + f y) x = D.laplacian f x := by
  have hnear := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hf.of_le (by norm_cast : (1 : ℕ∞ω) ≤ ∞))
  have hd : ∀ᶠ y in 𝓝 x,
      mvfderiv (𝓡 n) (fun z => c + f z) y = mvfderiv (𝓡 n) f y := by
    filter_upwards [hnear] with y hy
    rw [mvfderiv_fun_add mdifferentiableAt_const (hy.mdifferentiableAt (by simp)),
      mvfderiv_const, zero_add]
  unfold laplacian hessian hessianOnFields
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun y => mvfderiv (𝓡 n) (fun z => c + f z) y
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (g.orthonormalBasis x i) y)) =ᶠ[𝓝 x]
      (fun y => mvfderiv (𝓡 n) f y
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (g.orthonormalBasis x i) y)) := by
    filter_upwards [hd] with y hy
    rw [hy]
  rw [Poincare.mvfderiv_eq_of_eventuallyEq heq, hd.self_of_nhds]

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RiemannianMetric

theorem radius_comparison_of_half_le {a r s k : ℝ}
    (ha : 0 ≤ a) (hr : 0 < r) (hrs : r / 2 ≤ s) :
    a / s + a * k ≤ 2 * a / r + a * k := by
  have hs : 0 < s := (half_pos hr).trans_le hrs
  have h : a / s ≤ a / (r / 2) := div_le_div_of_nonneg_left ha (half_pos hr) hrs
  have heq : a / (r / 2) = 2 * a / r := by ring
  rw [heq] at h
  linarith

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]



theorem upper_support_of_inverse_branch
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (p q x : M)
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M} {R k : ℝ}
    (hbound : ∀ w ∈ Metric.ball 0 R, g.edist q (e w) ≤ ENNReal.ofReal ‖w‖)
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (m + 1))) M)
    (hsource : B.source ⊆ Metric.ball 0 R) (heB : EqOn e B B.source)
    (hB : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ B B.source)
    (hBi : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ B.symm B.target)
    (hzero : ∀ y ∈ B.target, B.symm y ≠ 0)
    {v : EuclideanSpace ℝ (Fin (m + 1))} (hv : v ∈ B.source) (hx : e v = x)
    (hsplit : (g.edist p q).toReal + ‖v‖ = (g.edist p x).toReal)
    (hhalf : (g.edist p x).toReal / 2 ≤ ‖v‖)
    (hgauss : ∀ w : EuclideanSpace ℝ (Fin (m + 1)),
      g.inner (e v) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e v v)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e v w) = inner ℝ v w)
    (hlap : D.laplacian (fun y => ‖B.symm y‖) x ≤ (m : ℝ) / ‖v‖ + (m : ℝ) * k) :
    ∃ (U : Set M) (rho : M → ℝ), IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ rho U ∧
      rho x = (g.edist p x).toReal ∧
      (∀ y ∈ U, (g.edist p y).toReal ≤ rho y) ∧
      g.inner x (D.gradient rho x) (D.gradient rho x) = 1 ∧
      D.laplacian rho x ≤ 2 * (m : ℝ) / (g.edist p x).toReal + (m : ℝ) * k := by
  subst x
  have hxB : B v = e v := (heB hv).symm
  have hxmem : e v ∈ B.target := hxB ▸ B.map_source hv
  have hrad : ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞
      (fun y => ‖B.symm y‖) B.target :=
    fun y hy => (smooth_inverse_branch_radius B hBi hy (hzero y hy)).contMDiffWithinAt
  have hradx := hrad.contMDiffAt (B.open_target.mem_nhds hxmem)
  have hv0 : v ≠ 0 := by
    simpa only [B.left_inv hv] using hzero (B v) (B.map_source hv)
  have hr : 0 < (g.edist p (e v)).toReal := by
    rw [← hsplit]
    exact add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg (norm_pos_iff.mpr hv0)
  refine ⟨B.target, (fun y => (g.edist p q).toReal + ‖B.symm y‖),
    B.open_target, hxmem, contMDiffOn_const.add hrad,
    g.inverse_branch_touches_distance B heB hv rfl hsplit, ?_, ?_, ?_⟩
  · intro y hy
    exact g.inverse_branch_distance_majorant p q hbound B hsource heB rfl hy
  · rw [D.gradient_const_add_at (hradx.mdifferentiableAt (by simp))]
    exact g.inner_gradient_inverse_branch D B heB hB hBi hv hv0 hgauss
  · rw [D.laplacian_const_add_at hradx]
    exact hlap.trans (radius_comparison_of_half_le (Nat.cast_nonneg m) hr hhalf)

end PoincareConjecture.RiemannianMetric
