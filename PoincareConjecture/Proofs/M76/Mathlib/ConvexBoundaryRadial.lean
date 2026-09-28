import PoincareConjecture.Proofs.M76.Mathlib.RadialSimplex
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.LocallyConvex.Separation

set_option autoImplicit false

open Set NormedSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem AffineIndependent.linearIndependent_of_linear_level {ι : Type*} {v : ι → E}
    (hv : AffineIndependent ℝ v) (L : E →ₗ[ℝ] ℝ) {c : ℝ} (hc : c ≠ 0)
    (hL : ∀ i, L (v i) = c) : LinearIndependent ℝ v := by
  rw [linearIndependent_iff']
  intro s w hw
  have hsum : ∑ i ∈ s, w i = 0 := by
    have h := congrArg L hw
    simp only [map_sum, map_smul, hL, smul_eq_mul, map_zero, ← Finset.sum_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hc
  exact hv s w hsum (by rw [Finset.weightedVSub_eq_linear_combination _ hsum]; exact hw)

theorem Convex.exists_positive_linear_level_of_subset_frontier {s t : Set E}
    (hs : Convex ℝ s) (hzero : (0 : E) ∈ interior s) (ht : Convex ℝ t)
    (hts : t ⊆ frontier s) :
    ∃ (L : E →ₗ[ℝ] ℝ) (c : ℝ), 0 < c ∧ ∀ x ∈ t, L x = c := by
  have hdisj : Disjoint (interior s) t := disjoint_left.mpr fun x hx hxt =>
    (hts hxt).2 hx
  obtain ⟨L, c, hLi, hLt⟩ := geometric_hahn_banach_open hs.interior isOpen_interior ht hdisj
  have hcl : ∀ x ∈ closure (interior s), L x ≤ c :=
    fun x hx => le_on_closure (fun y hy => (hLi y hy).le)
      L.continuous.continuousOn continuousOn_const hx
  have heq : closure (interior s) = closure s :=
    hs.closure_interior_eq_closure_of_nonempty_interior ⟨0, hzero⟩
  refine ⟨L.toLinearMap, c, by simpa using hLi 0 hzero, ?_⟩
  intro x hx
  exact le_antisymm (hcl x (heq.symm ▸ (hts hx).1)) (hLt x hx)

theorem AffineIndependent.linearIndependent_of_hull_subset_frontier {s t : Set E}
    (ht : AffineIndependent ℝ ((↑) : t → E)) (hs : Convex ℝ s)
    (hzero : (0 : E) ∈ interior s) (hts : convexHull ℝ t ⊆ frontier s) :
    LinearIndependent ℝ ((↑) : t → E) := by
  obtain ⟨L, c, hc, hL⟩ := hs.exists_positive_linear_level_of_subset_frontier
    hzero (convex_convexHull ℝ t) hts
  exact ht.linearIndependent_of_linear_level L hc.ne'
    (fun x => hL x (subset_convexHull ℝ t x.property))

theorem Convex.injOn_normalize_frontier {s : Set E} (hs : Convex ℝ s)
    (hzero : (0 : E) ∈ interior s) : InjOn (normalize : E → E) (frontier s) := by
  intro x hx y hy hxy
  have hnhds : s ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp hzero
  have hgx := (gauge_eq_one_iff_mem_frontier hs hnhds).mpr hx
  have hgy := (gauge_eq_one_iff_mem_frontier hs hnhds).mpr hy
  have hnorm : ‖x‖ = ‖y‖ := by
    have h := congrArg (gauge s) hxy
    simp only [NormedSpace.normalize, gauge_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      smul_eq_mul, hgx, hgy, mul_one] at h
    exact inv_injective h
  calc
    x = ‖x‖ • normalize x := (norm_smul_normalize x).symm
    _ = ‖y‖ • normalize y := by rw [hnorm, hxy]
    _ = y := norm_smul_normalize y

theorem IsCompact.exists_frontier_pos_smul {s : Set E} (hs : IsCompact s)
    (hcv : Convex ℝ s) (hzero : (0 : E) ∈ interior s) {x : E}
    (hx : x ∈ s) (hx0 : x ≠ 0) :
    ∃ y ∈ frontier s, ∃ r ∈ Ioc (0 : ℝ) 1, x = r • y := by
  have hnhds : s ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp hzero
  have hpos : 0 < gauge s x := (gauge_pos (absorbent_nhds_zero hnhds)
    (isVonNBounded_of_isBounded ℝ hs.isBounded)).mpr hx0
  have hle : gauge s x ≤ 1 := (gauge_le_one_iff_mem_closure hcv hnhds).mpr (subset_closure hx)
  refine ⟨(gauge s x)⁻¹ • x, ?_, gauge s x, ⟨hpos, hle⟩, ?_⟩
  · apply (gauge_eq_one_iff_mem_frontier hcv hnhds).mp
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hpos.le), smul_eq_mul,
      inv_mul_cancel₀ hpos.ne']
  · rw [smul_inv_smul₀ hpos.ne']
