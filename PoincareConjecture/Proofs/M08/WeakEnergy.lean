import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Topology

namespace PoincareConjecture.M08


theorem exists_weak_subsequence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (v : ℕ → H) (C : ℝ) (hbound : ∀ k, ‖v k‖ ≤ C) :
    ∃ w : H, ∃ φ : ℕ → ℕ, ‖w‖ ≤ C ∧ StrictMono φ ∧
      ∀ l : H →L[ℝ] ℝ,
        Tendsto (fun k ↦ l (v (φ k))) atTop (𝓝 (l w)) := by
  let ξ : ℕ → WeakDual ℝ H := fun k ↦
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (v k))
  have hξ : ∀ k, ξ k ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℝ H) C := by
    intro k
    simpa only [ξ, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hbound k
  obtain ⟨ζ, hζ, φ, hφ, hlim⟩ :=
    WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) C hξ
  let w : H := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual ζ)
  refine ⟨w, φ, ?_, hφ, ?_⟩
  · have hz : ‖WeakDual.toStrongDual ζ‖ ≤ C := by
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hζ
    simpa only [w, LinearIsometryEquiv.norm_map] using hz
  · intro l
    let z : H := (InnerProductSpace.toDual ℝ H).symm l
    have h := ((WeakDual.eval_continuous z).tendsto ζ).comp hlim
    have heval (q : H) : inner ℝ q z = l q := by
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    have hw : ζ z = l w := by
      change (WeakDual.toStrongDual ζ) z = l w
      rw [← InnerProductSpace.toDual_symm_apply]
      exact heval w
    have htest : Tendsto (fun k ↦ inner ℝ (v (φ k)) z) atTop (𝓝 (ζ z)) := h
    simpa only [heval, hw] using htest


theorem quadratic_energy_support {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (v : ℕ → H) (w : H) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ k, ‖v k‖ ≤ C)
    (hweak : ∀ l : H →L[ℝ] ℝ, Tendsto (fun k ↦ l (v k)) atTop (𝓝 (l w)))
    (Q : H →L[ℝ] H →L[ℝ] ℝ) (Qk : ℕ → H →L[ℝ] H →L[ℝ] ℝ)
    (hpositive : ∀ z, 0 ≤ Q z z)
    (hQ : Tendsto (fun k ↦ ‖Qk k - Q‖) atTop (𝓝 (0 : ℝ))) :
    ∃ ell : ℕ → ℝ, Tendsto ell atTop (𝓝 (Q w w)) ∧
      ∀ k, ell k ≤ Qk k (v k) (v k) := by
  have herror : Tendsto (fun k ↦ ‖Qk k - Q‖ * C ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have h := hQ.mul_const (C ^ 2)
    simpa only [zero_mul] using h
  have hlin := ((hweak (Q.flip w)).add (hweak (Q w))).sub
    (tendsto_const_nhds (x := Q w w) (f := atTop))
  have hlim : Tendsto
      (fun k ↦ Q (v k) w + Q w (v k) - Q w w - ‖Qk k - Q‖ * C ^ 2)
      atTop (𝓝 (Q w w)) := by
    simpa only [ContinuousLinearMap.flip_apply, add_sub_cancel_right, sub_zero] using
      hlin.sub herror
  refine ⟨_, hlim, ?_⟩
  intro k
  have hnonneg := hpositive (v k - w)
  simp only [map_sub, ContinuousLinearMap.sub_apply] at hnonneg
  have hnorm : |(Qk k - Q) (v k) (v k)| ≤ ‖Qk k - Q‖ * C ^ 2 := by
    calc
      |(Qk k - Q) (v k) (v k)| ≤ ‖Qk k - Q‖ * ‖v k‖ * ‖v k‖ :=
        (Qk k - Q).le_opNorm₂ _ _
      _ ≤ ‖Qk k - Q‖ * C * C := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hbound k) (Qk k - Q).opNorm_nonneg
        · exact hbound k
        · exact norm_nonneg _
        · exact mul_nonneg (Qk k - Q).opNorm_nonneg hC
      _ = _ := by ring
  have herr := (abs_le.mp hnorm).1
  simp only [ContinuousLinearMap.sub_apply] at herr
  linarith


theorem quadratic_energy_le_of_weak_limit {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (v : ℕ → H) (w : H) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ k, ‖v k‖ ≤ C)
    (hweak : ∀ l : H →L[ℝ] ℝ, Tendsto (fun k ↦ l (v k)) atTop (𝓝 (l w)))
    (Q : H →L[ℝ] H →L[ℝ] ℝ) (Qk : ℕ → H →L[ℝ] H →L[ℝ] ℝ)
    (hpositive : ∀ z, 0 ≤ Q z z)
    (hQ : Tendsto (fun k ↦ ‖Qk k - Q‖) atTop (𝓝 (0 : ℝ)))
    (e : ℕ → ℝ) (L : ℝ) (he : Tendsto e atTop (𝓝 L))
    (henergy : ∀ k, Qk k (v k) (v k) ≤ e k) : Q w w ≤ L := by
  obtain ⟨ell, hlim, hell⟩ := quadratic_energy_support v w C hC hbound hweak Q Qk hpositive hQ
  exact le_of_tendsto_of_tendsto hlim he (Filter.Eventually.of_forall
    (fun k ↦ (hell k).trans (henergy k)))


theorem finite_quadratic_action_le {ι : Type*} [Fintype ι] {H : ι → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedSpace ℝ (H i)]
    (v : ∀ i, ℕ → H i) (w : ∀ i, H i) (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i k, ‖v i k‖ ≤ C i)
    (hweak : ∀ i, ∀ l : H i →L[ℝ] ℝ,
      Tendsto (fun k ↦ l (v i k)) atTop (𝓝 (l (w i))))
    (Q : ∀ i, H i →L[ℝ] H i →L[ℝ] ℝ)
    (Qk : ∀ i, ℕ → H i →L[ℝ] H i →L[ℝ] ℝ)
    (hpositive : ∀ i z, 0 ≤ Q i z z)
    (hQ : ∀ i, Tendsto (fun k ↦ ‖Qk i k - Q i‖) atTop (𝓝 (0 : ℝ)))
    (potential action : ℕ → ℝ) (P L : ℝ)
    (hpotential : Tendsto potential atTop (𝓝 P)) (haction : Tendsto action atTop (𝓝 L))
    (henergy : ∀ k, (∑ i, Qk i k (v i k) (v i k)) + potential k ≤ action k) :
    (∑ i, Q i (w i) (w i)) + P ≤ L := by
  classical
  choose ell hlim hell using fun i ↦ quadratic_energy_support (v i) (w i) (C i) (hC i)
    (hbound i) (hweak i) (Q i) (Qk i) (hpositive i) (hQ i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ ↦ hlim i)
  apply le_of_tendsto_of_tendsto (hsum.add hpotential) haction
  apply Filter.Eventually.of_forall
  intro k
  exact (add_le_add (Finset.sum_le_sum (fun i _ ↦ hell i k)) le_rfl).trans (henergy k)

end PoincareConjecture.M08
