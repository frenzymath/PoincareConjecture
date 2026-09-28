import PoincareConjecture.Proofs.M76.Mathlib.EuclideanPlaneTopology
import PoincareConjecture.Proofs.M76.Mathlib.ClosedConeProjectionBound










set_option autoImplicit false

open Set

namespace Submodule

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]




def IsSecantTransverse (K : Submodule ℝ E) (S : Set E) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x ∈ S, ∀ y ∈ S,
    c * ‖x - y‖ ≤ ‖(x - y) - K.starProjection (x - y)‖




theorem isSecantTransverse_ker_of_lower_bound (Q : E →L[ℝ] F) {S : Set E}
    {c : ℝ} (hc : 0 < c)
    (hb : ∀ x ∈ S, ∀ y ∈ S, c * ‖x - y‖ ≤ ‖Q x - Q y‖) :
    Q.ker.IsSecantTransverse S := by
  have hden : 0 < ‖Q‖ + 1 := by positivity
  refine ⟨c / (‖Q‖ + 1), div_pos hc hden, fun x hx y hy => ?_⟩
  have hk : Q (Q.ker.starProjection (x - y)) = 0 :=
    Q.ker.starProjection_apply_mem (x - y)
  have hop : ‖Q x - Q y‖ ≤ ‖Q‖ * ‖(x - y) - Q.ker.starProjection (x - y)‖ := by
    calc
      ‖Q x - Q y‖ = ‖Q ((x - y) - Q.ker.starProjection (x - y))‖ := by
        rw [map_sub, hk, map_sub, sub_zero]
      _ ≤ _ := Q.le_opNorm ((x - y) - Q.ker.starProjection (x - y))
  calc
    c / (‖Q‖ + 1) * ‖x - y‖ = (c * ‖x - y‖) / (‖Q‖ + 1) := by ring
    _ ≤ ‖(x - y) - Q.ker.starProjection (x - y)‖ := by
      apply (div_le_iff₀ hden).mpr
      have hn := norm_nonneg ((x - y) - Q.ker.starProjection (x - y))
      have hxy := hb x hx y hy
      nlinarith



theorem IsSecantTransverse.injOn {K : Submodule ℝ E} {S : Set E}
    (hK : K.IsSecantTransverse S) (Q : E →L[ℝ] F) (hker : Q.ker = K) :
    InjOn Q S := by
  obtain ⟨c, hc, hb⟩ := hK
  intro x hx y hy he
  have hxy : x - y ∈ K := by
    rw [← hker]
    change Q (x - y) = 0
    rw [map_sub, he, sub_self]
  have h := hb x hx y hy
  rw [K.starProjection_eq_self_iff.mpr hxy, sub_self, norm_zero] at h
  have hz : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)



theorem IsSecantTransverse.mono {K : Submodule ℝ E} {S T : Set E}
    (hK : K.IsSecantTransverse T) (hST : S ⊆ T) : K.IsSecantTransverse S := by
  obtain ⟨c, hc, hb⟩ := hK
  exact ⟨c, hc, fun x hx y hy => hb x (hST hx) y (hST hy)⟩



theorem isSecantTransverse_of_projector_dist_le {K L : Submodule ℝ E} {S : Set E}
    {c : ℝ} (hc : 0 < c)
    (hb : ∀ x ∈ S, ∀ y ∈ S, c * ‖x - y‖ ≤ ‖(x - y) - K.starProjection (x - y)‖)
    (hKL : ‖K.starProjection - L.starProjection‖ ≤ c / 2) :
    L.IsSecantTransverse S := by
  refine ⟨c / 2, half_pos hc, fun x hx y hy => ?_⟩
  have hop := (K.starProjection - L.starProjection).le_opNorm (x - y)
  have hd := norm_sub_norm_le ((x - y) - K.starProjection (x - y))
    ((x - y) - L.starProjection (x - y))
  have he : (x - y - K.starProjection (x - y)) -
      (x - y - L.starProjection (x - y)) =
      -(K.starProjection (x - y) - L.starProjection (x - y)) := by abel
  rw [he, norm_neg] at hd
  have hmul := mul_le_mul_of_nonneg_right hKL (norm_nonneg (x - y))
  have hxy := hb x hx y hy
  change ‖K.starProjection (x - y) - L.starProjection (x - y)‖ ≤ _ at hop
  linarith

end Submodule

namespace Geometry.EuclideanSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]



theorem isOpen_isSecantTransverse (S : Set E) :
    IsOpen {K : EuclideanSubspace E | K.subspace.IsSecantTransverse S} := by
  apply isOpen_iff_mem_nhds.mpr
  intro K hK
  obtain ⟨c, hc, hb⟩ := hK
  have hn := (continuous_projector E).continuousAt.preimage_mem_nhds
    (Metric.ball_mem_nhds K.subspace.starProjection (half_pos hc))
  apply Filter.mem_of_superset hn
  intro L hL
  apply Submodule.isSecantTransverse_of_projector_dist_le hc hb
  exact (by simpa only [mem_preimage, Metric.mem_ball, dist_eq_norm, norm_sub_rev]
    using hL : ‖K.subspace.starProjection - L.subspace.starProjection‖ < c / 2).le

end Geometry.EuclideanSubspace
