import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Growth.BoundaryDistance














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}



theorem not_forall_carrier_subset_next_core (S : ℕ → CapCertificate g)
    {B ε : ℝ} (hB : ∀ n, (S n).cap_constant ≤ B)
    (hε : ∀ n, (S n).epsilon = ε) :
    ¬ ∀ n, (S n).carrier ⊆ (S (n + 1)).core := by
  intro hcore
  obtain ⟨p, hp0⟩ := (S 0).core_nonempty
  have hp : ∀ n, p ∈ (S n).carrier := by
    intro n
    induction n with
    | zero => exact (S 0).core_subset_carrier hp0
    | succ n ih => exact (S (n + 1)).core_subset_carrier (hcore n ih)
  let D := (S 0).connection
  have hBpos : 0 < B := (S 0).cap_constant_pos.trans_le (hB 0)
  have hεpos : 0 < ε := hε 0 ▸ (S 0).epsilon_pos
  have hscalar : 0 < D.scalarCurvature p := (S 0).scalar_pos p (hp 0)
  let δ : ℝ := (0.9 : ℝ) * (B * D.scalarCurvature p) ^ (-1 / 2 : ℝ) * ε⁻¹
  let U : ℝ := B * D.scalarCurvature p ^ (-1 / 2 : ℝ)
  have hδ : 0 < δ := by
    exact mul_pos (mul_pos (by norm_num)
      (Real.rpow_pos_of_pos (mul_pos hBpos hscalar) _)) (inv_pos.mpr hεpos)
  let r : ℕ → ℝ≥0∞ := fun n => ⨅ z ∈ (S n).carrierᶜ, g.edist p z
  have hbound (n : ℕ) : r n < ENNReal.ofReal U := by
    let q := (S (n + 1)).boundary_neck.center
    have hq : q ∈ (S (n + 1)).boundary_sphere :=
      (S (n + 1)).boundary_eq_neck_sphere.symm ▸
        (S (n + 1)).boundary_neck.center_on_central_sphere
    have hqout : q ∈ (S n).carrierᶜ :=
      fun hqn => Set.disjoint_left.mp (S (n + 1)).disjoint_core_boundary (hcore n hqn) hq
    have hd := (S (n + 1)).edist_lt_at_point (hB (n + 1)) (hp (n + 1))
      ((S (n + 1)).boundary_subset hq)
    rw [(S (n + 1)).connection.scalarCurvature_eq D p] at hd
    exact (iInf_le_of_le q (iInf_le _ hqout)).trans_lt hd
  have hgrowth (n : ℕ) : r n + ENNReal.ofReal δ ≤ r (n + 1) := by
    have hscale := ((S (n + 1)).uniform_bounds_at_point D (hB (n + 1)) (hp (n + 1))).2.2
    have hδbound : ENNReal.ofReal δ ≤ ENNReal.ofReal
        ((0.9 : ℝ) * (S (n + 1)).boundary_neck.scale * (S (n + 1)).epsilon⁻¹) := by
      apply ENNReal.ofReal_le_ofReal
      rw [hε (n + 1)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscale.le (by norm_num)) (inv_pos.mpr hεpos).le
    exact (add_le_add le_rfl hδbound).trans
      ((S (n + 1)).complement_distance_gain_of_carrier_subset_core (S n) (hcore n) (hp n))
  have hnat (n : ℕ) : ENNReal.ofReal ((n : ℝ) * δ) ≤ r n := by
    induction n with
    | zero => simp only [Nat.cast_zero, zero_mul, ENNReal.ofReal_zero]; exact zero_le
    | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg n) hδ.le) hδ.le]
      exact (add_le_add ih le_rfl).trans (hgrowth n)
  obtain ⟨n, hn⟩ := exists_nat_gt (U / δ)
  have hlt := (hnat n).trans_lt (hbound n)
  have hreal : (n : ℝ) * δ < U :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg n) hδ.le)).mp hlt
  exact (not_lt_of_ge ((div_lt_iff₀ hδ).mp hn).le) hreal

end PoincareConjecture.CapCertificate
