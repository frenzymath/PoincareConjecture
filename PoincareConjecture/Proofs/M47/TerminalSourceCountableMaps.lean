import PoincareConjecture.Proofs.M47.TerminalSourceCountableScale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : ℕ → Type u} {rho : ℕ → ℝ} {N : ℕ → ℕ}

noncomputable def terminalSourceCountableMap (hrho : ∀ j, 0 < rho j)
    (e : ∀ k j, j ≤ k → Fin (N j + 1) → terminalSourceCountableDomain (rho j) → M k)
    (k j : ℕ) (i : Fin (N j + 1)) : terminalSourceCountableDomain (rho j) → M k :=
  if hjk : j ≤ k then e k j hjk i
  else e k 0 (Nat.zero_le k) 0 ∘ terminalSourceCountableScaleMap (hrho 0) (hrho j)

theorem terminalSourceCountableMap_good (hrho : ∀ j, 0 < rho j)
    (e : ∀ k j, j ≤ k → Fin (N j + 1) → terminalSourceCountableDomain (rho j) → M k)
    {k j : ℕ} (hjk : j ≤ k) (i : Fin (N j + 1)) :
    terminalSourceCountableMap hrho e k j i = e k j hjk i := by
  simp only [terminalSourceCountableMap, dif_pos hjk]

theorem terminalSourceCountableMap_eventually_good (hrho : ∀ j, 0 < rho j)
    (e : ∀ k j, j ≤ k → Fin (N j + 1) → terminalSourceCountableDomain (rho j) → M k)
    (j : ℕ) (i : Fin (N j + 1)) :
    ∀ᶠ k in atTop, ∃ hjk : j ≤ k,
      terminalSourceCountableMap hrho e k j i = e k j hjk i := by
  filter_upwards [eventually_ge_atTop j] with k hk
  exact ⟨hk, terminalSourceCountableMap_good hrho e hk i⟩

variable [∀ k, MetricSpace (M k)] [∀ k, ChartedSpace E (M k)]

theorem terminalSourceCountableMap_geometry (hrho : ∀ j, 0 < rho j)
    (e : ∀ k j, j ≤ k → Fin (N j + 1) → terminalSourceCountableDomain (rho j) → M k)
    (hopen : ∀ k j hjk i, Topology.IsOpenEmbedding (e k j hjk i))
    (hsmooth : ∀ k j hjk i, IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e k j hjk i)) :
    ∀ k j i, Topology.IsOpenEmbedding (terminalSourceCountableMap hrho e k j i) ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (terminalSourceCountableMap hrho e k j i) := by
  intro k j i
  by_cases hjk : j ≤ k
  · rw [terminalSourceCountableMap_good hrho e hjk i]
    exact ⟨hopen k j hjk i, hsmooth k j hjk i⟩
  · rw [terminalSourceCountableMap, dif_neg hjk]
    obtain ⟨ho, hs⟩ := terminalSourceCountableScaleMap_geometry (hrho 0) (hrho j)
    refine ⟨(hopen k 0 (Nat.zero_le k) 0).comp ho, ?_⟩
    intro x
    exact (hs x).comp (𝓡 3) (M k)
      (hsmooth k 0 (Nat.zero_le k) 0 (terminalSourceCountableScaleMap (hrho 0) (hrho j) x))

omit [∀ k, ChartedSpace E (M k)] in

theorem terminalSourceCountableMap_distances (hrho : ∀ j, 0 < rho j)
    (e : ∀ k j, j ≤ k → Fin (N j + 1) → terminalSourceCountableDomain (rho j) → M k)
    (hdist : ∀ k j hjk i x y,
      (1 / 2 : ℝ) * dist x y ≤ dist (e k j hjk i x) (e k j hjk i y) ∧
        dist (e k j hjk i x) (e k j hjk i y) ≤ (3 / 2 : ℝ) * dist x y) :
    (∀ j, 0 < terminalSourceCountableScaleFactor (rho 0) (rho j) / 2) ∧
      ∀ k j i x y,
        (terminalSourceCountableScaleFactor (rho 0) (rho j) / 2) * dist x y ≤
            dist (terminalSourceCountableMap hrho e k j i x)
              (terminalSourceCountableMap hrho e k j i y) ∧
          dist (terminalSourceCountableMap hrho e k j i x)
              (terminalSourceCountableMap hrho e k j i y) ≤ (3 / 2 : ℝ) * dist x y := by
  refine ⟨fun j => half_pos (terminalSourceCountableScaleFactor_bounds (hrho 0) (hrho j)).1,
    ?_⟩
  intro k j i x y
  have hlambda := (terminalSourceCountableScaleFactor_bounds (hrho 0) (hrho j)).2.1
  by_cases hjk : j ≤ k
  · rw [terminalSourceCountableMap_good hrho e hjk i]
    obtain ⟨hl, hu⟩ := hdist k j hjk i x y
    refine ⟨?_, hu⟩
    apply le_trans _ hl
    exact mul_le_mul_of_nonneg_right (by linarith only [hlambda]) dist_nonneg
  · simp only [terminalSourceCountableMap, dif_neg hjk, Function.comp_apply]
    obtain ⟨hl, hu⟩ := hdist k 0 (Nat.zero_le k) 0
      (terminalSourceCountableScaleMap (hrho 0) (hrho j) x)
      (terminalSourceCountableScaleMap (hrho 0) (hrho j) y)
    rw [terminalSourceCountableScaleMap_dist] at hl hu
    refine ⟨by nlinarith only [hl], hu.trans ?_⟩
    have hscale := mul_le_mul_of_nonneg_right hlambda (dist_nonneg (x := x) (y := y))
    nlinarith only [hscale]

omit [∀ k, ChartedSpace E (M k)] in

theorem terminalSourceCountableMap_base_distances (hrho : ∀ j, 0 < rho j)
    (e : ∀ k j, j ≤ k → Fin (N j + 1) → terminalSourceCountableDomain (rho j) → M k)
    (p : ∀ k, M k) (B : ℕ → ℝ)
    (hzero : ∀ k, e k 0 (Nat.zero_le k) 0 (terminalSourceCountableZero (hrho 0)) = p k)
    (hupper : ∀ k j hjk i x y,
      dist (e k j hjk i x) (e k j hjk i y) ≤ (3 / 2 : ℝ) * dist x y)
    (hbase : ∀ k j hjk i x, dist (p k) (e k j hjk i x) ≤ B j) :
    (∀ k j i x, dist (p k) (terminalSourceCountableMap hrho e k j i x) ≤
      max (B j) (rho 0 / 2)) ∧
      ∀ k j i x j' i' y,
        dist (terminalSourceCountableMap hrho e k j i x)
            (terminalSourceCountableMap hrho e k j' i' y) ≤
          max (B j) (rho 0 / 2) + max (B j') (rho 0 / 2) := by
  have hbound (k j : ℕ) (i : Fin (N j + 1)) (x : terminalSourceCountableDomain (rho j)) :
      dist (p k) (terminalSourceCountableMap hrho e k j i x) ≤ max (B j) (rho 0 / 2) := by
    by_cases hjk : j ≤ k
    · rw [terminalSourceCountableMap_good hrho e hjk i]
      exact (hbase k j hjk i x).trans (le_max_left _ _)
    · simp only [terminalSourceCountableMap, dif_neg hjk, Function.comp_apply]
      have hu := hupper k 0 (Nat.zero_le k) 0 (terminalSourceCountableZero (hrho 0))
        (terminalSourceCountableScaleMap (hrho 0) (hrho j) x)
      rw [hzero k] at hu
      have hd : dist (terminalSourceCountableZero (hrho 0))
          (terminalSourceCountableScaleMap (hrho 0) (hrho j) x) =
            ‖(terminalSourceCountableScaleMap (hrho 0) (hrho j) x : E)‖ := by
        change dist (0 : E) _ = _
        exact dist_zero_left _
      rw [hd] at hu
      have hn := terminalSourceCountableScaleMap_norm_lt (hrho 0) (hrho j) x
      have hsmall : dist (p k)
          (e k 0 (Nat.zero_le k) 0 (terminalSourceCountableScaleMap (hrho 0) (hrho j) x)) ≤
          rho 0 / 2 := by nlinarith only [hu, hn, hrho 0]
      exact hsmall.trans (le_max_right _ _)
  refine ⟨hbound, ?_⟩
  intro k j i x j' i' y
  calc
    _ ≤ dist (terminalSourceCountableMap hrho e k j i x) (p k) +
        dist (p k) (terminalSourceCountableMap hrho e k j' i' y) := dist_triangle _ _ _
    _ = dist (p k) (terminalSourceCountableMap hrho e k j i x) +
        dist (p k) (terminalSourceCountableMap hrho e k j' i' y) := by rw [dist_comm]
    _ ≤ _ := add_le_add (hbound k j i x) (hbound k j' i' y)

end PoincareConjecture.M47
