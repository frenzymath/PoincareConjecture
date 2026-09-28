import PoincareConjecture.Proofs.M34.Standard.ReverseBallLocalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

theorem inverse_tangentNorm_le_of_forward_lower_bound
    {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N]
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    (e : OpenPartialHomeomorph M N)
    (hf : ContMDiffOn (𝓡 n) (𝓡 m) 1 e e.source)
    (hi : ContMDiffOn (𝓡 m) (𝓡 n) 1 e.symm e.target)
    {y : N} (hy : y ∈ e.target) {C : ℝ}
    (hbound : ∀ w : TangentSpace (𝓡 n) (e.symm y),
      g.tangentNorm (e.symm y) w ≤ C * h.tangentNorm (e (e.symm y))
        (mfderiv (𝓡 n) (𝓡 m) e (e.symm y) w))
    (v : TangentSpace (𝓡 m) y) :
    g.tangentNorm (e.symm y) (mfderiv (𝓡 m) (𝓡 n) e.symm y v) ≤
      C * h.tangentNorm y v := by
  have hx := e.map_target hy
  have huf : UniqueMDiffWithinAt (𝓡 n) e.source (e.symm y) :=
    e.open_source.uniqueMDiffWithinAt hx
  have hui : UniqueMDiffWithinAt (𝓡 m) e.target y :=
    e.open_target.uniqueMDiffWithinAt hy
  have hfa := ((hf (e.symm y) hx).contMDiffAt
    (e.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have hia := ((hi y hy).contMDiffAt
    (e.open_target.mem_nhds hy)).mdifferentiableAt (by simp)
  have hcomp := mfderivWithin_comp y hfa.mdifferentiableWithinAt
    hia.mdifferentiableWithinAt (fun z hz => e.map_target hz) hui
  have hright : ∀ z ∈ e.target, (e ∘ e.symm) z = id z := fun z hz => e.right_inv hz
  rw [mfderivWithin_congr_of_mem hright hy, mfderivWithin_id hui,
    mfderivWithin_eq_mfderiv huf hfa, mfderivWithin_eq_mfderiv hui hia] at hcomp
  have hid := congrArg (fun A => A v) hcomp.symm
  have hb := hbound (mfderiv (𝓡 m) (𝓡 n) e.symm y v)
  have hv : mfderiv (𝓡 n) (𝓡 m) e (e.symm y)
      (mfderiv (𝓡 m) (𝓡 n) e.symm y v) = v := hid
  rw [hv] at hb
  have hn : h.tangentNorm (e (e.symm y)) v = h.tangentNorm y v :=
    congrArg (fun z : N => h.tangentNorm z
      (show EuclideanSpace ℝ (Fin m) from v)) (e.right_inv hy)
  exact hb.trans_eq (congrArg (fun z => C * z) hn)

theorem ball_subset_image_ball_of_forward_tangentNorm_le
    {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ N] [T3Space M]
    (g : RiemannianMetric n M) (h : RiemannianMetric m N)
    (e : OpenPartialHomeomorph M N)
    (hf : ContMDiffOn (𝓡 n) (𝓡 m) 1 e e.source)
    (hi : ContMDiffOn (𝓡 m) (𝓡 n) 1 e.symm e.target)
    {o : M} (ho : o ∈ e.source) {r C : ℝ} (hC : 0 < C)
    (hcover : h.ball (e o) r ⊆ e.target)
    (hbound : ∀ x ∈ e.source, g.edist o x ≤ ENNReal.ofReal (C * r) →
      ∀ v : TangentSpace (𝓡 n) x,
        g.tangentNorm x v ≤ C * h.tangentNorm (e x)
          (mfderiv (𝓡 n) (𝓡 m) e x v)) :
    h.ball (e o) r ⊆ e '' (g.ball o (C * r) ∩ e.source) := by
  apply g.ball_subset_image_ball_of_guarded_inverse_tangentNorm_le h e hi ho hC hcover
  intro y hy hdist v
  exact g.inverse_tangentNorm_le_of_forward_lower_bound h e hf hi hy
    (hbound (e.symm y) (e.map_target hy) hdist) v

end PoincareConjecture.RiemannianMetric
