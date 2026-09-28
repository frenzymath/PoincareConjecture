import PoincareConjecture.Proofs.M76.Horizon.CompactCore.GeneralPosition.FrontierChartStars
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open Set Metric unitInterval

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_protected_vertex_motion
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N Y F O : Set X}
    (hN : PLDomain e N) (hY : IsOpen Y) (hcut : Y ∩ frontier N = F)
    (hO : IsOpen O) {x : X} (hx : x ∈ Y) (hxO : x ∈ O) :
    ∃ p : C(I, X), p 0 = x ∧ (∀ t, p t ∈ O ∩ Y) ∧
      (x ∉ F → ∀ t, p t = x) ∧
      ∀ t : I, 0 < (t : ℝ) → p t ∉ F := by
  by_cases hxF : x ∈ F
  · obtain ⟨B, hxB, hBY, _, hkind⟩ :=
      hN.exists_protected_frontier_chart hY hcut x hx
    rcases hkind with hdis | ⟨ell, v, hv, _, hfront⟩
    · exact False.elim (disjoint_left.mp hdis hxB hxF)
    have hzero : ell (B x) = 0 := (hfront x hxB).mp hxF
    let a : ℝ → V3 := fun t => B x + t • v
    have ha : Continuous a := continuous_const.add (continuous_id.smul continuous_const)
    have hopen : IsOpen (a ⁻¹' (B.target ∩ B.symm ⁻¹' O)) :=
      (B.isOpen_inter_preimage_symm hO).preimage ha
    have h0 : (0 : ℝ) ∈ a ⁻¹' (B.target ∩ B.symm ⁻¹' O) := by
      simpa only [a, zero_smul, add_zero, mem_preimage, mem_inter_iff,
        B.left_inv hxB] using And.intro (B.map_source hxB) hxO
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hopen 0 h0
    have hsmall (t : I) : a ((t : ℝ) * (r / 2)) ∈ B.target ∩ B.symm ⁻¹' O := by
      apply hrsub
      rw [mem_ball, Real.dist_eq, sub_zero,
        abs_of_nonneg (mul_nonneg t.property.1 (by positivity))]
      nlinarith [t.property.2]
    let p : C(I, X) := ⟨fun t => B.symm (a ((t : ℝ) * (r / 2))),
      B.symm.continuousOn.comp_continuous
        (ha.comp (continuous_subtype_val.mul continuous_const)) (fun t => (hsmall t).1)⟩
    refine ⟨p, ?_, ?_, fun h => False.elim (h hxF), ?_⟩
    · exact (by change B.symm (B x + (0 * (r / 2)) • v) = x
                simpa using B.left_inv hxB)
    · intro t
      exact ⟨(hsmall t).2, hBY (B.symm.map_source (hsmall t).1)⟩
    · intro t ht hmem
      have hz := (hfront (p t) (B.symm.map_source (hsmall t).1)).mp hmem
      change ell (B (B.symm (a ((t : ℝ) * (r / 2))))) = 0 at hz
      rw [B.right_inv (hsmall t).1] at hz
      have hheight (s : ℝ) : ell (a s) = s := by
        dsimp only [a]
        rw [add_comm (B x), ← vadd_eq_add, ContinuousAffineMap.map_vadd,
          map_smul, hv, smul_eq_mul, mul_one, hzero, vadd_eq_add, add_zero]
      rw [hheight] at hz
      exact (ne_of_gt (mul_pos ht (by positivity))) hz
  · exact ⟨ContinuousMap.const I x, rfl, fun _ => ⟨hxO, hx⟩,
      fun _ _ => rfl, fun _ _ => hxF⟩

end PoincareConjecture.M76
