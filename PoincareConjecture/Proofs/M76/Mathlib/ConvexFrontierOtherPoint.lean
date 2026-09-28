import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryExtension










set_option autoImplicit false

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem IsCompact.exists_ne_frontier_point {C : Set E}
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (x : frontier C) : ∃ p : frontier C, p ≠ x := by
  obtain ⟨_, e, _⟩ := hC.exists_compatible_unitBall_models hcv hne
  let v : E := e x
  have hv : ‖v‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using (e x).property
  let y : sphere (0 : E) 1 :=
    ⟨-v, by simpa only [mem_sphere, dist_zero_right, norm_neg] using hv⟩
  refine ⟨e.symm y, ?_⟩
  intro h
  have hneg : -v = v := by
    have heq := congrArg (fun z : frontier C => (e z : E)) h
    simpa only [e.apply_symm_apply] using heq
  have htwo : (2 : ℝ) • v = 0 := by
    rw [two_smul]
    exact (congrArg (fun z : E => z + v) hneg.symm).trans (neg_add_cancel v)
  have hvzero : v = 0 := (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  rw [hvzero, norm_zero] at hv
  exact zero_ne_one hv
