import PoincareConjecture.Proofs.M76.Dehn.Mathlib.NestedFiniteCoordinateCubes
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcBranchLinks









set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)

theorem exists_finite_branch_outer_collar
    (J P : SimplicialComplex ℝ V3) (hP : P.faces.Finite)
    (hzero : (0 : V3) ∈ interior J.space) :
    ∃ (ρ : ℝ) (P₀ : SimplicialComplex ℝ V3), 0 < ρ ∧
      closedBall (0 : V3) ρ ⊆ interior J.space ∧ P₀.faces.Finite ∧
      P₀.space = P.space \ ball (0 : V3) ρ ∧
      P.space ∩ frontier J.space ⊆ P₀.space := by
  classical
  obtain ⟨r₀, hr₀, hball₀⟩ := Metric.isOpen_iff.mp isOpen_interior 0 hzero
  let ρ := r₀ / 2
  have hρ : 0 < ρ := half_pos hr₀
  have hclosed : closedBall (0 : V3) ρ ⊆ interior J.space :=
    (closedBall_subset_ball (half_lt_self hr₀)).trans hball₀
  have hball : ball (0 : V3) ρ ⊆ interior J.space := ball_subset_closedBall.trans hclosed
  let A (i : Fin 3 × Bool) : V3 →ᵃ[ℝ] ℝ :=
    if i.2 then AffineMap.const ℝ V3 ρ - (LinearMap.proj i.1).toAffineMap
    else AffineMap.const ℝ V3 ρ + (LinearMap.proj i.1).toAffineMap
  choose L hL hLs using fun i : Fin 3 × Bool ↦
    P.exists_finite_triangulation_inter_halfspaces hP {A i}
  obtain ⟨P₀, hP₀, hP₀s, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion L hL
  have hspace : P₀.space = P.space \ ball (0 : V3) ρ := by
    rw [hP₀s]
    ext x
    simp only [mem_iUnion, hLs, mem_inter_iff, mem_ofPred_eq,
      Finset.mem_singleton, forall_eq, mem_sdiff, mem_ball, dist_zero_right]
    constructor
    · rintro ⟨⟨i, b⟩, hxP, hxA⟩
      refine ⟨hxP, fun hxnorm ↦ ?_⟩
      have hi := (pi_norm_lt_iff hρ).mp hxnorm i
      rw [Real.norm_eq_abs, abs_lt] at hi
      cases b with
      | false =>
        have hxa : ρ + x i ≤ 0 := by
          simpa only [A, Bool.false_eq_true, if_false, AffineMap.coe_add, Pi.add_apply,
            AffineMap.const_apply, LinearMap.coe_toAffineMap, LinearMap.proj_apply] using hxA
        linarith
      | true =>
        have hxa : ρ - x i ≤ 0 := by
          simpa only [A, if_true, AffineMap.coe_sub, Pi.sub_apply,
            AffineMap.const_apply, LinearMap.coe_toAffineMap, LinearMap.proj_apply] using hxA
        linarith
    · rintro ⟨hxP, hxnorm⟩
      have hn : ¬ ∀ i : Fin 3, ‖x i‖ < ρ :=
        fun h ↦ hxnorm ((pi_norm_lt_iff hρ).mpr h)
      obtain ⟨i, hi⟩ := not_forall.mp hn
      have hi' : ¬ (-ρ < x i ∧ x i < ρ) := by
        simpa only [Real.norm_eq_abs, abs_lt] using hi
      by_cases hn : x i ≤ -ρ
      · refine ⟨(i, false), hxP, ?_⟩
        change ρ + x i ≤ 0
        linarith
      · refine ⟨(i, true), hxP, ?_⟩
        change ρ - x i ≤ 0
        have hp : ρ ≤ x i := le_of_not_gt (fun h ↦ hi' ⟨lt_of_not_ge hn, h⟩)
        linarith
  refine ⟨ρ, P₀, hρ, hclosed, hP₀, hspace, ?_⟩
  intro x hx
  exact hspace.symm.subset ⟨hx.1, fun h ↦ hx.2.2 (hball h)⟩

end PoincareConjecture.M76.Dehn
