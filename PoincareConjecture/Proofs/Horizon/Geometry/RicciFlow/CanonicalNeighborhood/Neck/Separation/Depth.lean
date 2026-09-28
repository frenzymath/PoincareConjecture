import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Axial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Cutoff
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.DerivativeLipschitz
import Mathlib.Analysis.Calculus.Deriv.Support









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Bundle Topology NNReal

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem abs_mvfderiv_axialCutoff_le {φ : ℝ → ℝ} {a b C : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹)
    (hφ : ContDiff ℝ ∞ φ) (hs : support φ ⊆ Icc a b)
    (hC : 0 ≤ C) (hbound : ∀ s, |deriv φ s| ≤ C)
    (x : M) (v : TangentSpace (𝓡 3) x) :
    |mvfderiv (𝓡 3) (N.axialCutoff φ) x v| ≤
      (C / (N.scale * Real.sqrt (1 - N.epsilon))) * g.tangentNorm x v := by
  have hfactor : 0 < N.scale * Real.sqrt (1 - N.epsilon) :=
    mul_pos N.scale_pos (Real.sqrt_pos.mpr (by linarith [N.epsilon_lt_half]))
  by_cases hx : x ∈ N.carrier
  · rw [← N.connection.inner_gradient, N.gradient_axialCutoff N.connection hφ hx]
    simp only [map_smul, smul_apply, smul_eq_mul,
      N.connection.inner_gradient, abs_mul]
    have hax : |mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x v| ≤
        g.tangentNorm x v / (N.scale * Real.sqrt (1 - N.epsilon)) :=
      (le_div_iff₀ hfactor).mpr (by
      simpa only [mul_comm] using N.axial_mvfderiv_bound hx v)
    calc
      _ ≤ C * (g.tangentNorm x v / (N.scale * Real.sqrt (1 - N.epsilon))) :=
        mul_le_mul (hbound _) hax (abs_nonneg _) hC
      _ = _ := by ring
  · let K := N.coordinate_map '' (univ ×ˢ Icc a b)
    have hK : IsCompact K := N.isCompact_coordinate_slab ha hb
    have hxK : x ∉ K := by
      rintro ⟨z, hz, rfl⟩
      exact hx (N.coordinate_map_mem ⟨mem_univ _, ha.trans_le hz.2.1,
        hz.2.2.trans_lt hb⟩)
    have he : N.axialCutoff φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
      by_contra hn
      exact hy (N.support_axialCutoff_subset hs hn)
    unfold mvfderiv
    rw [he.mfderiv_eq]
    simp only [mfderiv_const, ContinuousLinearMap.comp_zero, zero_apply, abs_zero]
    exact mul_nonneg (div_nonneg hC hfactor.le) (Real.sqrt_nonneg _)



theorem abs_axialCutoff_sub_le [PreconnectedSpace M]
    {φ : ℝ → ℝ} {a b C : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹)
    (hφ : ContDiff ℝ ∞ φ) (hs : support φ ⊆ Icc a b)
    (hC : 0 < C) (hbound : ∀ s, |deriv φ s| ≤ C) (x y : M) :
    |N.axialCutoff φ x - N.axialCutoff φ y| ≤
      (C / (N.scale * Real.sqrt (1 - N.epsilon))) * (g.edist x y).toReal := by
  have hfactor : 0 < N.scale * Real.sqrt (1 - N.epsilon) :=
    mul_pos N.scale_pos (Real.sqrt_pos.mpr (by linarith [N.epsilon_lt_half]))
  let K : ℝ≥0 := ⟨C / (N.scale * Real.sqrt (1 - N.epsilon)),
    (div_pos hC hfactor).le⟩
  exact g.abs_sub_le_mul_toReal_edist_of_derivative_bound
    ((N.contMDiff_axialCutoff ha hb hφ hs).of_le (by simp))
    (K := K) (div_pos hC hfactor)
    (N.abs_mvfderiv_axialCutoff_le ha hb hφ hs hC.le hbound) x y

end PoincareConjecture.EpsilonNeck
