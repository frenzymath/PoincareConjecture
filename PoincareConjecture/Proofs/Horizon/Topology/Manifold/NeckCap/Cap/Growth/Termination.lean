import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Growth.Step

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.CapCertificate

theorem exists_cap_growth_termination_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M} {B ε : ℝ},
        0 < ε → ε ≤ ε₀ → ∀ S : ℕ → CapCertificate g,
        (∀ n, (S n).cap_constant ≤ B) → (∀ n, (S n).epsilon = ε) →
        ¬ ∀ n, (S n).carrier ⊆ (S (n + 1)).carrier ∧
          (frontier (S n).carrier ∩ (S (n + 1)).closed_core).Nonempty := by
  obtain ⟨ε₀, hε₀, hsmall, hstep⟩ := exists_nested_frontier_contact_distance_gain.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g B ε hεpos hε S hB hsame hnested
  obtain ⟨p, hp0⟩ := (S 0).core_nonempty
  have hp : ∀ n, p ∈ (S n).carrier := by
    intro n
    induction n with
    | zero => exact (S 0).core_subset_carrier hp0
    | succ n ih => exact (hnested n).1 ih
  let D := (S 0).connection
  have hBpos : 0 < B := (S 0).cap_constant_pos.trans_le (hB 0)
  have hscalar : 0 < D.scalarCurvature p := (S 0).scalar_pos p (hp 0)
  let δ : ℝ := (0.38 : ℝ) * (B * D.scalarCurvature p) ^ (-1 / 2 : ℝ) * ε⁻¹
  let U : ℝ := B * D.scalarCurvature p ^ (-1 / 2 : ℝ)
  have hδ : 0 < δ :=
    mul_pos (mul_pos (by norm_num)
      (Real.rpow_pos_of_pos (mul_pos hBpos hscalar) _)) (inv_pos.mpr hεpos)
  have hU : 0 < U := mul_pos hBpos (Real.rpow_pos_of_pos hscalar _)
  let r : ℕ → ℝ≥0∞ := fun n => ⨅ z ∈ (S n).carrierᶜ, g.edist p z
  have hbound (n : ℕ) : r n ≤ ENNReal.ofReal U := by
    obtain ⟨q, hq, _⟩ := (hnested n).2
    have hout : q ∈ (S n).carrierᶜ := ((S n).carrier_open.frontier_eq ▸ hq).2
    have hd := (S n).edist_le_of_mem_closure (hB n) (hp n) (frontier_subset_closure hq)
    rw [(S n).connection.scalarCurvature_eq D p] at hd
    exact (iInf_le_of_le q (iInf_le _ hout)).trans hd
  have hgrowth (n : ℕ) : r n + ENNReal.ofReal δ ≤ r (n + 1) := by
    have hscale := ((S (n + 1)).uniform_bounds_at_point D (hB (n + 1)) (hp (n + 1))).2.2
    have hδbound : ENNReal.ofReal δ ≤ ENNReal.ofReal
        ((0.38 : ℝ) * (S (n + 1)).boundary_neck.scale * ε⁻¹) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscale.le (by norm_num)) (inv_pos.mpr hεpos).le
    exact (add_le_add le_rfl hδbound).trans
      (hstep hεpos hε (S n) (S (n + 1)) (hsame n) (hsame (n + 1))
        (hnested n).1 (hnested n).2 (hp n))
  have hnat (n : ℕ) : ENNReal.ofReal ((n : ℝ) * δ) ≤ r n := by
    induction n with
    | zero => simp only [Nat.cast_zero, zero_mul, ENNReal.ofReal_zero]; exact zero_le
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg n) hδ.le) hδ.le]
      exact (add_le_add ih le_rfl).trans (hgrowth n)
  obtain ⟨n, hn⟩ := exists_nat_gt (U / δ)
  have hnum : U < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
  have hlt : ENNReal.ofReal U < ENNReal.ofReal ((n : ℝ) * δ) :=
    (ENNReal.ofReal_lt_ofReal_iff (hU.trans hnum)).mpr hnum
  exact (not_lt_of_ge ((hnat n).trans (hbound n))) hlt

end PoincareConjecture.CapCertificate
