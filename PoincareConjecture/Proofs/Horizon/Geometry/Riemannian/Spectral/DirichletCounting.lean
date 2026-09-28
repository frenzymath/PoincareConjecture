import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Spectrum.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Spectral.Counting.Partition
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Spectral.Counting.ChartMollification
import PoincareConjecture.Proofs.Horizon.Analysis.Spectral.Counting.Absorption
import PoincareConjecture.Proofs.Horizon.Analysis.Spectral.Counting.Summability













set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace

attribute [local instance] Classical.propDecidable

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

variable (D : LeviCivitaData g) (Ω : Set M) (hn : 0 < n)
  (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))

theorem energyEigenfunction_inner (i j : EigenIndex D Ω) :
    ⟪energyEigenfunction D Ω hn hΩ hc i, energyEigenfunction D Ω hn hΩ hc j⟫_ℝ =
      if i = j then 1 + eigenvalue D Ω i else 0 := by
  classical
  rw [energyEigenfunction_equation, ← inner_toDomainL2 hΩ.measurableSet,
    toDomainL2_energyEigenfunction, toDomainL2_energyEigenfunction,
    orthonormal_iff_ite.mp (eigenbasis D Ω hn hΩ hc).orthonormal]
  split_ifs <;> simp

theorem norm_energyEigenfunction_sq (i : EigenIndex D Ω) :
    ‖energyEigenfunction D Ω hn hΩ hc i‖ ^ 2 = 1 + eigenvalue D Ω i := by
  rw [← real_inner_self_eq_norm_sq, energyEigenfunction_inner]
  simp

theorem norm_sum_energyEigenfunction_sq (s : Finset (EigenIndex D Ω))
    (a : EigenIndex D Ω → ℝ) :
    ‖∑ i ∈ s, a i • energyEigenfunction D Ω hn hΩ hc i‖ ^ 2 =
      ∑ i ∈ s, (1 + eigenvalue D Ω i) * a i ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    energyEigenfunction_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    ring
  · intro j hj hji
    simp [hji]
  · exact fun h => (h hi).elim

theorem norm_toDomainL2_sum_energyEigenfunction_sq (s : Finset (EigenIndex D Ω))
    (a : EigenIndex D Ω → ℝ) :
    ‖toDomainL2 D Ω (∑ i ∈ s, a i • energyEigenfunction D Ω hn hΩ hc i)‖ ^ 2 =
      ∑ i ∈ s, a i ^ 2 := by
  simp only [map_sum, map_smul, toDomainL2_energyEigenfunction]
  rw [← real_inner_self_eq_norm_sq,
    (eigenbasis D Ω hn hΩ hc).orthonormal.inner_sum]
  simp only [conj_trivial, ← pow_two]


theorem norm_sum_energyEigenfunction_sq_le (s : Finset (EigenIndex D Ω))
    (a : EigenIndex D Ω → ℝ) {Λ : ℝ}
    (hs : ∀ i ∈ s, eigenvalue D Ω i ≤ Λ) :
    ‖∑ i ∈ s, a i • energyEigenfunction D Ω hn hΩ hc i‖ ^ 2 ≤
      (1 + Λ) *
        ‖toDomainL2 D Ω (∑ i ∈ s, a i • energyEigenfunction D Ω hn hΩ hc i)‖ ^ 2 := by
  rw [norm_sum_energyEigenfunction_sq, norm_toDomainL2_sum_energyEigenfunction_sq,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_right (add_le_add le_rfl (hs i hi)) (sq_nonneg _)

open Counting Poincare.Analysis.Spectral.Counting

include hn hΩ hc

set_option backward.isDefEq.respectTransparency false in


theorem exists_eigenvalue_finset_counting :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 0 ≤ Λ → ∀ s : Finset (EigenIndex D Ω),
      (∀ i ∈ s, eigenvalue D Ω i ≤ Λ) →
        (s.card : ℝ) ≤ C * (1 + Λ) ^ ((n : ℝ) / 2) := by
  classical
  obtain ⟨J, ρ, hρc, hρs⟩ := exists_finite_chart_partition (n := n) hc
  let L := partitionLocalization D Ω hΩ hc ρ hρc hρs
  let S (j : J) : Set (EuclideanSpace ℝ (Fin n)) :=
    Metric.cthickening 1
      ((chartAt (EuclideanSpace ℝ (Fin n)) (j : M)) '' tsupport (ρ j : M → ℝ))
  have hS (j : J) : MeasurableSet (S j) := Metric.isClosed_cthickening.measurableSet
  have hSvol (j : J) : volume (S j) ≠ ⊤ :=
    (((hρc j).image_of_continuousOn
      ((chartAt (EuclideanSpace ℝ (Fin n)) (j : M)).continuousOn.mono
        (hρs j))).cthickening).measure_ne_top
  obtain ⟨C, hC, hrec⟩ := exists_partition_norm_bound D Ω hΩ hc ρ hρc hρs
  have herr (j : J) := exists_norm_chartLocalization_sub_mollifyOn_sq_le_energy
    (D := D) (Ω := Ω) hΩ hc
    (chartAt (EuclideanSpace ℝ (Fin n)) (j : M)).symm
    contMDiffOn_chart_symm contMDiffOn_chart
    (ρ j) (ρ j).contMDiff (hρc j) (hρs j)
  choose R hR herr using herr
  let B (j : J) := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (S j) *
    (‖L j‖ ^ 2 * ((2 : ℝ) ^ n /
      (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.closedBall 0 1)))
  let A := 2 * C * ∑ j, R j
  let T := 2 * C * ∑ j, B j
  have hA : 0 ≤ A := by
    exact mul_nonneg (mul_nonneg (by norm_num) hC) (Finset.sum_nonneg fun j _ => hR j)
  let C' := 2 * T * (2 * (A + 1)) ^ ((n : ℝ) / 2)
  refine ⟨max C' 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun Λ hΛ s hs => ?_⟩
  have hraw (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
      (s.card : ℝ) ≤ A * ε ^ 2 * (1 + Λ) * s.card + T / ε ^ n := by
    let z (i : EigenIndex D Ω) (j : J) :=
      mollifyOn (S j) (hS j) (hSvol j) hε (L j (eigenbasis D Ω hn hΩ hc i))
    have hrec' (i : EigenIndex D Ω) (_hi : i ∈ s) :
        1 ≤ C * ∑ j, ‖L j (eigenbasis D Ω hn hΩ hc i)‖ ^ 2 := by
      have h := hrec (energyEigenfunction D Ω hn hΩ hc i)
      rw [toDomainL2_energyEigenfunction, (eigenbasis D Ω hn hΩ hc).orthonormal.norm_eq_one,
        one_pow] at h
      exact h
    have herr' (i : EigenIndex D Ω) (hi : i ∈ s) :
        ∑ j, ‖L j (eigenbasis D Ω hn hΩ hc i) - z i j‖ ^ 2 ≤
          (∑ j, R j) * ε ^ 2 * (1 + Λ) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j hj
      have h := herr j ε hε hε1 (energyEigenfunction D Ω hn hΩ hc i)
      dsimp only at h
      rw [toDomainL2_energyEigenfunction, norm_energyEigenfunction_sq] at h
      exact h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hs i hi))
        (mul_nonneg (hR j) (sq_nonneg ε)))
    have htrace : ∑ j, ∑ i ∈ s, ‖z i j‖ ^ 2 ≤ (∑ j, B j) / ε ^ n := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro j hj
      have ht := sum_norm_mollifyOn_map_sq_le (S j) (hS j) (hSvol j) hε (L j)
        (eigenbasis D Ω hn hΩ hc).orthonormal s
      dsimp only [z]
      convert! ht using 1
      dsimp [B]
      ring
    have h := card_le_error_add_trace s (fun i j => L j (eigenbasis D Ω hn hΩ hc i)) z
      hC hrec' herr' htrace
    convert! h using 1
    dsimp [A, T]
    ring
  have hcount := le_rpow_of_le_error_add_inverse_pow n (Nat.cast_nonneg s.card) hA
    (show 1 ≤ 1 + Λ by linarith) hraw
  exact hcount.trans (mul_le_mul_of_nonneg_right (le_max_left C' 1)
    (Real.rpow_nonneg (by linarith) _))



theorem exists_eigenvalue_counting :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 0 ≤ Λ →
      {i : EigenIndex D Ω | eigenvalue D Ω i ≤ Λ}.Finite ∧
        (({i : EigenIndex D Ω | eigenvalue D Ω i ≤ Λ}.ncard : ℕ) : ℝ) ≤
          C * (1 + Λ) ^ ((n : ℝ) / 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_eigenvalue_finset_counting D Ω hn hΩ hc
  refine ⟨C, hC, fun Λ hΛ => ?_⟩
  apply finite_ncard_le_of_finset_card_le
  intro s hs
  exact hbound Λ hΛ s (fun i hi => hs hi)



theorem summable_eigenvalue_weighted_exp (t : ℝ) (ht : 0 < t) (m : ℕ) :
    Summable (fun i : EigenIndex D Ω =>
      (1 + eigenvalue D Ω i) ^ m * Real.exp (-t * eigenvalue D Ω i)) := by
  obtain ⟨C, hC, hbound⟩ := exists_eigenvalue_finset_counting D Ω hn hΩ hc
  exact summable_weighted_exp_of_counting (eigenvalue D Ω)
    (eigenvalue_nonneg D Ω hn hΩ hc) C hC.le ((n : ℝ) / 2) hbound ht m

end PoincareConjecture.LeviCivitaData.Dirichlet
