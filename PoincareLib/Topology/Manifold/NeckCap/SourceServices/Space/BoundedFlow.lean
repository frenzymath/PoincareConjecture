import Mathlib.Analysis.ODE.ExistUnique

/-!
# Global integral curves of bounded Lipschitz vector fields

Finite-interval Picard solutions agree on overlaps by ODE uniqueness,
giving a global solution. This supplies the analytic first step toward
the restricted ambient isotopies in Hatcher, Notes on Basic 3-Manifold
Topology, Theorem 1.1 and Lemmas 1.2-1.3, pp. 1-3.

See `proof-work/tasks/M25/schoenflies/derivations/2026-09-21-bounded-flow.md`.
-/

set_option autoImplicit false

open Set Metric Filter
open scoped NNReal Topology

namespace PoincareMT.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (f : E → E) {K L : ℝ≥0}

/-- A bounded Lipschitz field has a solution on any prescribed finite
symmetric time interval, by Mathlib's Picard-Lindelof theorem. -/
theorem boundedField_intervalSolution (hK : LipschitzWith K f)
    (hL : ∀ x, ‖f x‖ ≤ L) (x : E) (r : ℝ) (hr : 0 < r) :
    ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Ioo (-r) r, HasDerivAt γ (f (γ t)) t := by
  let t₀ : Icc (-r) r := ⟨0, by constructor <;> linarith⟩
  let a : ℝ≥0 := ⟨(L : ℝ) * r, mul_nonneg L.coe_nonneg hr.le⟩
  have hPicard : IsPicardLindelof (fun _ : ℝ => f) t₀ x a 0 L K := {
    lipschitzOnWith := fun _ _ => hK.lipschitzOnWith
    continuousOn := fun _ _ => continuousOn_const
    norm_le := fun _ _ y _ => hL y
    mul_max_le := by
      simp only [t₀, a, sub_zero, zero_sub, neg_neg, max_self, NNReal.coe_zero]
      exact le_rfl }
  obtain ⟨γ, hγ, hd⟩ := hPicard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨γ, hγ, fun t ht => ?_⟩
  exact (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- Finite-interval solutions of a bounded Lipschitz field join to a
global integral curve. Only comparisons within their actual domains are used. -/
theorem boundedField_globalSolution (hK : LipschitzWith K f)
    (hL : ∀ x, ‖f x‖ ≤ L) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (f (γ t)) t := by
  classical
  choose γ hγ0 hγode using fun r : {r : ℝ // 0 < r} =>
    boundedField_intervalSolution f hK hL x r.1 r.2
  have hcompat (r s : {r : ℝ // 0 < r}) :
      EqOn (γ r) (γ s) (Ioo (-min r.1 s.1) (min r.1 s.1)) := by
    have hm : 0 < min r.1 s.1 := lt_min r.2 s.2
    have hrsub : Ioo (-min r.1 s.1) (min r.1 s.1) ⊆ Ioo (-r.1) r.1 :=
      Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
    have hssub : Ioo (-min r.1 s.1) (min r.1 s.1) ⊆ Ioo (-s.1) s.1 :=
      Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
    exact ODE_solution_unique_of_mem_Ioo
      (v := fun _ : ℝ => f) (s := fun _ => univ)
      (fun _ _ => hK.lipschitzOnWith)
      (show (0 : ℝ) ∈ Ioo (-min r.1 s.1) (min r.1 s.1) by
        constructor <;> linarith)
      (fun t ht => ⟨hγode r t (hrsub ht), mem_univ _⟩)
      (fun t ht => ⟨hγode s t (hssub ht), mem_univ _⟩)
      ((hγ0 r).trans (hγ0 s).symm)
  let radius (t : ℝ) : {r : ℝ // 0 < r} := ⟨|t| + 1, by positivity⟩
  let F : ℝ → E := fun t => γ (radius t) t
  have hlocal (r : {r : ℝ // 0 < r}) : EqOn F (γ r) (Ioo (-r.1) r.1) := by
    intro t ht
    apply hcompat (radius t) r
    apply abs_lt.mp
    exact lt_min (by dsimp [radius]; linarith) (abs_lt.mpr ht)
  refine ⟨F, hγ0 (radius 0), fun t => ?_⟩
  have ht : t ∈ Ioo (-(radius t).1) (radius t).1 := by
    apply abs_lt.mp
    dsimp [radius]
    linarith
  have heq : F =ᶠ[𝓝 t] γ (radius t) :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2) (hlocal (radius t))
  simpa only [hlocal (radius t) ht] using
    (hγode (radius t) t ht).congr_of_eventuallyEq heq

omit [CompleteSpace E] in
/-- Two global curves of a Lipschitz autonomous field with the same
initial value agree, by Mathlib's ODE uniqueness theorem. -/
theorem boundedField_solution_unique (hK : LipschitzWith K f) {γ η : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (f (γ t)) t)
    (hη : ∀ t, HasDerivAt η (f (η t)) t) (h0 : γ 0 = η 0) : γ = η :=
  ODE_solution_unique_univ (v := fun _ : ℝ => f) (s := fun _ => univ)
    (fun _ => hK.lipschitzOnWith) (fun t => ⟨hγ t, mem_univ _⟩)
    (fun t => ⟨hη t, mem_univ _⟩) h0

end PoincareMT.M25.Topology3D
