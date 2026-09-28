import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Bounded










noncomputable section
set_option autoImplicit false

open Set Metric

namespace Poincare.Topology


theorem not_nonempty_homeomorph_compact_prod_real_euclidean_three
    {C : Type*} [TopologicalSpace C] [CompactSpace C] [Nonempty C] :
    ¬ Nonempty ((C × ℝ) ≃ₜ EuclideanSpace ℝ (Fin 3)) := by
  rintro ⟨e⟩
  let f : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => (e.symm x).2
  have hf : Continuous f := continuous_snd.comp e.symm.continuous
  have hc : IsCompact (range (fun c : C => e (c, (0 : ℝ)))) :=
    isCompact_range (e.continuous.comp (continuous_id.prodMk continuous_const))
  obtain ⟨r, hr, hcr⟩ := hc.isBounded.exists_pos_norm_lt
  have hfc := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) r).image hf
  obtain ⟨a, ha, hfa⟩ := hfc.isBounded.exists_pos_norm_lt
  let c : C := Classical.choice inferInstance
  have hout (s : ℝ) (hs : ‖s‖ = a) : r ≤ ‖e (c, s)‖ := by
    by_contra h
    have hin : e (c, s) ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) r := by
      simpa only [mem_closedBall, dist_zero_right] using (not_le.mp h).le
    have hlt := hfa (f (e (c, s))) ⟨e (c, s), hin, rfl⟩
    have heq : f (e (c, s)) = s := by simp [f]
    rw [heq, hs] at hlt
    exact (lt_irrefl a) hlt
  have hneg := hout (-a) (by simp [abs_of_pos ha])
  have hpos := hout a (by simp [abs_of_pos ha])
  have hconn := isPreconnected_norm_ge
    (E := EuclideanSpace ℝ (Fin 3))
    (by rw [← Module.finrank_eq_rank]; norm_num) hr
  obtain ⟨x, hx, hfx⟩ := hconn.intermediate_value hneg hpos hf.continuousOn
    (show (0 : ℝ) ∈ Icc (f (e (c, -a))) (f (e (c, a))) by
      simp [f, ha.le])
  have heq : e ((e.symm x).1, (0 : ℝ)) = x := by
    have : (e.symm x).2 = 0 := hfx
    simpa only [← this] using e.apply_symm_apply x
  have hlt := hcr x ⟨(e.symm x).1, heq⟩
  exact (not_lt_of_ge hx) hlt

end Poincare.Topology
