import PoincareConjecture.Proofs.M30.Generalized.BlowupSubsequence
import PoincareConjecture.Proofs.M30.Generalized.Restriction
import Mathlib.Order.Filter.Finite
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

theorem exists_diagonal_controlled_cylinders
    (S : GeneralizedBlowupSequence.{u}) (T B : ℕ → ℝ)
    (hprefix : ∀ n : ℕ, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ j : ℕ, j ≤ n → ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
        ∀ᶠ k : ℕ in atTop,
          Nonempty (ControlledBlowupCylinder S (phi k) A (T j) (B j) eta)) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∀ j : ℕ, ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
        ∀ᶠ k : ℕ in atTop,
          Nonempty (ControlledBlowupCylinder S (sigma k) A (T j) (B j) eta) := by
  let W (n : ℕ) : ℝ := (n : ℝ) + 1
  let error (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hW (n : ℕ) : 0 < W n := by dsimp [W]; positivity
  have herror (n : ℕ) : 0 < error n := by dsimp [error]; positivity
  have hrows : ∀ n : ℕ, ∃ᶠ k : ℕ in atTop,
      ∀ j : ℕ, j ≤ n →
        Nonempty (ControlledBlowupCylinder S k (W n) (T j) (B j) (error n)) := by
    intro n
    obtain ⟨phi, hphi, hphiC⟩ := hprefix n
    have hfinite : ∀ᶠ k : ℕ in atTop, ∀ j ∈ Finset.range (n + 1),
        Nonempty (ControlledBlowupCylinder S (phi k) (W n) (T j) (B j)
          (error n)) := by
      apply (Filter.eventually_all_finset (Finset.range (n + 1))).2
      intro j hj
      exact hphiC j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
        (W n) (hW n) (error n) (herror n)
    apply frequently_atTop.2
    intro N
    obtain ⟨k, hkN, hk⟩ := ((eventually_ge_atTop N).and hfinite).exists
    refine ⟨phi k, hkN.trans (hphi.id_le k), ?_⟩
    intro j hj
    exact hk j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
  obtain ⟨sigma, hsigma, hrow⟩ := extraction_forall_of_frequently hrows
  refine ⟨sigma, hsigma, ?_⟩
  intro j A _hA eta heta
  have hlarge : ∀ᶠ k : ℕ in atTop, A ≤ W k := by
    filter_upwards [(tendsto_natCast_atTop_atTop :
      Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop A)] with k hk
    dsimp only [W]
    linarith
  have hsmall : ∀ᶠ k : ℕ in atTop, error k ≤ eta := by
    filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (Iio_mem_nhds heta)] with k hk
    exact le_of_lt hk
  filter_upwards [eventually_ge_atTop j, hlarge, hsmall] with k hjk hAk hek
  obtain ⟨E⟩ := hrow k j hjk
  have hball : S.baseBall (sigma k) A ⊆ S.baseBall (sigma k) (W k) := by
    intro x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right hAk (Real.sqrt_nonneg _)))
  refine ⟨{
    embedding := Cylinder.restrict E.embedding Subset.rfl hball
    zero_identity := fun hs x hx => E.zero_identity hs x (hball hx)
    curvature_bound := fun s hs x hx => E.curvature_bound s hs x (hball hx)
    negative_curvature_bound := ?_ }⟩
  intro s hs x hx
  exact (E.negative_curvature_bound s hs x (hball hx)).trans
    (mul_le_mul_of_nonneg_right hek (S.base_scalar_pos (sigma k)).le)

theorem exists_reindexed_diagonal_controlled_cylinders
    (S : GeneralizedBlowupSequence.{u}) (T B : ℕ → ℝ)
    (hprefix : ∀ n : ℕ, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∀ j : ℕ, j ≤ n → ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
        ∀ᶠ k : ℕ in atTop,
          Nonempty (ControlledBlowupCylinder S (phi k) A (T j) (B j) eta)) :
    ∃ sigma : ℕ → ℕ, ∃ hsigma : StrictMono sigma,
      ∀ j : ℕ, ∀ A : ℝ, 0 < A → ∀ eta : ℝ, 0 < eta →
        ∀ᶠ k : ℕ in atTop,
          Nonempty (ControlledBlowupCylinder
            (reindexedBlowupSequence S sigma hsigma) k A (T j) (B j) eta) := by
  obtain ⟨sigma, hsigma, hC⟩ := exists_diagonal_controlled_cylinders S T B hprefix
  refine ⟨sigma, hsigma, ?_⟩
  intro j A hA eta heta
  filter_upwards [hC j A hA eta heta] with k hk
  obtain ⟨E⟩ := hk
  exact ⟨{
    embedding := E.embedding
    zero_identity := E.zero_identity
    curvature_bound := E.curvature_bound
    negative_curvature_bound := E.negative_curvature_bound }⟩

end PoincareConjecture.M30
