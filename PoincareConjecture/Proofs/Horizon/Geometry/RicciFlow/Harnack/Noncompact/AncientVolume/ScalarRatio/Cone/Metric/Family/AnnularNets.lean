import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.Family.DenseDirections









set_option autoImplicit false
open Set Filter
open scoped Topology

namespace Poincare.AncientVolume.ScalarRatio



theorem exists_finite_ray_net_on_rescaled_annulus
    {X : Type*} [MetricSpace X] {p : X}
    (η : ℕ → basedMinimizingRays p)
    (hnets : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ x : X, dist p x = L →
        ∃ j ≤ N, dist x (rayExtension (η j) L) / L < ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∃ N : ℕ, ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ x : X, |dist p x / L - 1| ≤ δ →
        ∃ j ≤ N, dist x (rayExtension (η j) L) / L < ε := by
  obtain ⟨N, A, hA, hnet⟩ := hnets (ε / 4) (by positivity)
  let δ := min (1 / 2 : ℝ) (ε / 4)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  refine ⟨δ, hδ, hδhalf, N, 2 * A, by positivity, ?_⟩
  intro L hL x hx
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity : 0 < 2 * A) hL
  have hnear := abs_le.mp hx
  have hlower : L / 2 ≤ dist p x := by
    have h : (1 / 2 : ℝ) ≤ dist p x / L := by linarith
    have := (le_div_iff₀ hLpos).mp h
    linarith
  have hupper : dist p x ≤ 3 * L / 2 := by
    have h : dist p x / L ≤ (3 / 2 : ℝ) := by linarith
    have := (div_le_iff₀ hLpos).mp h
    linarith
  have hxpos : 0 < dist p x := lt_of_lt_of_le (by positivity) hlower
  obtain ⟨j, hj, hclose⟩ := hnet (dist p x) (by linarith) x rfl
  have hclose' := (div_lt_iff₀ hxpos).mp hclose
  have hradial : |dist p x - L| ≤ δ * L := by
    have heq : (dist p x / L - 1) * L = dist p x - L := by
      field_simp
    calc
      |dist p x - L| = |(dist p x / L - 1) * L| := congrArg abs heq.symm
      _ = |dist p x / L - 1| * L := by rw [abs_mul, abs_of_pos hLpos]
      _ ≤ δ * L := mul_le_mul_of_nonneg_right hx hLpos.le
  have htri := dist_triangle x (rayExtension (η j) (dist p x)) (rayExtension (η j) L)
  rw [rayExtension_dist (η j) hxpos.le hLpos.le] at htri
  refine ⟨j, hj, (div_lt_iff₀ hLpos).mpr ?_⟩
  have hsmall := mul_le_mul_of_nonneg_right hδε hLpos.le
  have hbound := mul_le_mul_of_nonneg_left hupper (show 0 ≤ ε / 4 by positivity)
  nlinarith



theorem eventually_finite_ray_net_on_rescaled_annulus
    {X : Type*} [MetricSpace X] {p : X}
    (η : ℕ → basedMinimizingRays p)
    (hnets : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ L₀ : ℝ, 0 < L₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ x : X, dist p x = L →
        ∃ j ≤ N, dist x (rayExtension (η j) L) / L < ε)
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∃ N : ℕ, ∀ᶠ k in atTop,
      ∀ x : X, |dist p x / L k - 1| ≤ δ →
        ∃ j ≤ N, dist x (rayExtension (η j) (L k)) / L k < ε := by
  obtain ⟨δ, hδ, hδhalf, N, A, _, hcover⟩ :=
    exists_finite_ray_net_on_rescaled_annulus η hnets hε
  exact ⟨δ, hδ, hδhalf, N, (hL.eventually_ge_atTop A).mono fun k hk => hcover _ hk⟩

end Poincare.AncientVolume.ScalarRatio
