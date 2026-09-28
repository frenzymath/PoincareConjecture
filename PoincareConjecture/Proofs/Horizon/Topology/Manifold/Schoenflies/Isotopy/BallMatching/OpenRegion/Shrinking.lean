import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.ChartShrinking



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies



theorem exists_supported_ball_shrinking_in_open_region {n : Nat}
    (A : Diffeomorph (𝓡 n) (𝓡 n)
      (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞)
    (O U : Set (EuclideanSpace Real (Fin n))) (hO : IsOpen O) (hU : IsOpen U)
    (hAO : A '' closedBall 0 1 ⊆ O) (hAU : A 0 ∈ U) :
    ∃ K : Set (EuclideanSpace Real (Fin n)), IsCompact K ∧ K ⊆ O ∧
      ∃ D : Diffeomorph (𝓡 n) (𝓡 n)
        (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) ∞,
        (∀ x ∉ K, D x = x) ∧ D '' (A '' closedBall 0 1) ⊆ U := by
  let E := EuclideanSpace Real (Fin n)
  let e := A.toHomeomorph.toOpenPartialHomeomorph.trans (OpenPartialHomeomorph.ofSet O hO)
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := A.contMDiff.contMDiffOn
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := A.symm.contMDiff.contMDiffOn
  have hball : closedBall (0 : E) 1 ⊆ e.source :=
    fun x hx => ⟨mem_univ _, hAO ⟨x, hx, rfl⟩⟩
  obtain ⟨epsilon, hepsilon, hsub⟩ :=
    Metric.isOpen_iff.mp (hU.preimage A.continuous) 0 hAU
  let c := min epsilon 1 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by dsimp [c]; have := min_le_right epsilon 1; linarith
  have hce : c < epsilon := by dsimp [c]; have := min_le_left epsilon 1; linarith
  obtain ⟨K, hK, hKe, Phi, _, _, hfix, hmotion⟩ :=
    exists_supported_chart_shrinking_isotopy e he hei (by norm_num : (0 : Real) < 1)
      hc hc1 hball
  refine ⟨K, hK, fun x hx => (hKe hx).1, Phi 1, hfix 1, ?_⟩
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hm : Phi 1 (A x) = A (c • x) := by
    have hm := hmotion 1 (by simp) x hx
    change Phi 1 (A x) = A (Real.exp (1 * Real.log c) • x) at hm
    simpa only [one_mul, Real.exp_log hc] using hm
  rw [hm]
  apply hsub
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hx' : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  exact (mul_le_of_le_one_right hc.le hx').trans_lt hce

end Poincare.Manifold.Schoenflies
