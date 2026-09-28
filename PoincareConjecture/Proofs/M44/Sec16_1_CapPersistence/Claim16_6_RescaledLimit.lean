import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CompactnessFeedCoordinates
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_ExhaustionBounds
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RescaledLimitFlow
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.Operator
















set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

local notation "E" => StandardCapSpace
local notation "V" => SpacetimeBounds.MetricCoefficient 3

noncomputable local instance rescaledLimitCoefficientNorm : NormedAddCommGroup V :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance rescaledLimitCoefficientSpace : NormedSpace ℝ V :=
  ContinuousLinearMap.toNormedSpace





theorem exists_glued_coordinate_limit
    {U : ℕ → Set (ℝ × E)} (hmono : Monotone U)
    {f : ℕ → ℝ × E → V} {b : ℕ → ℝ × E → V}
    (hb : ∀ i, CompactSmoothConvergenceOn f (b i) atTop (U i)) :
    ∃ B : ℝ × E → V,
      (∀ i, EqOn B (b i) (U i)) ∧
      CompactSmoothConvergenceOn f B atTop (⋃ i, U i) := by
  classical
  let B : ℝ × E → V := fun p =>
    if hp : p ∈ ⋃ i, U i then b (Classical.choose (mem_iUnion.mp hp)) p else 0
  have heq (i : ℕ) : EqOn B (b i) (U i) := by
    intro p hp
    have hpU : p ∈ ⋃ j, U j := mem_iUnion.mpr ⟨i, hp⟩
    simp only [B, dif_pos hpU]
    exact coordinate_limits_eq_on_overlap
      (hb (Classical.choose (mem_iUnion.mp hpU))) (hb i)
      ⟨Classical.choose_spec (mem_iUnion.mp hpU), hp⟩
  have hcompact {K : Set (ℝ × E)} (hK : IsCompact K) (hKU : K ⊆ ⋃ i, U i) :
      ∃ i, K ⊆ U i :=
    hK.elim_directed_cover U (fun i => (hb i).isOpen) hKU
      (fun i j => ⟨max i j, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩)
  refine ⟨B, heq, ⟨isOpen_iUnion (fun i => (hb i).isOpen), ?_, ?_, ?_⟩⟩
  · intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact (((hb i).smooth.contDiffAt ((hb i).isOpen.mem_nhds hi)).congr_of_eventuallyEq
      (eventuallyEq_of_mem ((hb i).isOpen.mem_nhds hi) (heq i))).contDiffWithinAt
  · intro K hK hKU
    obtain ⟨i, hKi⟩ := hcompact hK hKU
    exact (hb i).eventually_smooth K hK hKi
  · intro m K hK hKU
    obtain ⟨i, hKi⟩ := hcompact hK hKU
    apply ((hb i).jets m K hK hKi).congr_right
    intro p hp
    exact ((eventuallyEq_of_mem ((hb i).isOpen.mem_nhds (hKi hp))
      (heq i)).iteratedFDeriv ℝ m).self_of_nhds.symm





theorem exists_rescaled_coordinate_limit
    {U : ℕ → Set (ℝ × E)} (hU : ∀ i, IsOpen (U i)) (hmono : Monotone U)
    (f : ℕ → ℝ × E → V)
    (hsmooth : ∀ i, ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (f k) (U i))
    (hbound : ∀ i K, IsCompact K → K ⊆ U i → ∀ m : ℕ,
      ∃ C : ℝ, ∀ᶠ k in atTop, ∀ p ∈ K,
        ‖iteratedFDeriv ℝ m (f k) p‖ ≤ C) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧ ∃ B : ℝ × E → V,
      CompactSmoothConvergenceOn (fun k => f (sigma k)) B atTop (⋃ i, U i) := by
  obtain ⟨sigma, hsigma, b, hb⟩ := exists_common_coordinate_limit hU f hsmooth hbound
  obtain ⟨B, _, hB⟩ := exists_glued_coordinate_limit hmono hb
  exact ⟨sigma, hsigma, B, hB⟩





theorem standard_spacetime_buffers_exhaust
    (g0 : StandardInitialMetric) (J : Set ℝ) :
    (⋃ i : ℕ, J ×ˢ g0.metric.ball 0 ((i : ℝ) + 1)) = J ×ˢ (univ : Set E) := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact ⟨hi.1, mem_univ _⟩
  · intro hp
    obtain ⟨R, _, hx⟩ := exists_standard_ball_radius g0 p.2
    obtain ⟨i, hi⟩ := exists_nat_gt R
    refine mem_iUnion.mpr ⟨i, hp.1, ?_⟩
    exact hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith))






theorem exists_rescaled_limit_on_standard_space
    (g0 : StandardInitialMetric) {J : Set ℝ} (hJ : IsOpen J)
    (f : ℕ → ℝ × E → V)
    (hsmooth : ∀ R : ℝ, 0 < R → ∀ᶠ k in atTop,
      ContDiffOn ℝ ∞ (f k) (J ×ˢ g0.metric.ball 0 R))
    (hbound : ∀ R : ℝ, 0 < R → ∀ K : Set (ℝ × E),
      IsCompact K → K ⊆ J ×ˢ g0.metric.ball 0 R → ∀ m : ℕ,
        ∃ C : ℝ, ∀ᶠ k in atTop, ∀ p ∈ K, ‖iteratedFDeriv ℝ m (f k) p‖ ≤ C) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧ ∃ B : ℝ × E → V,
      CompactSmoothConvergenceOn (fun k => f (sigma k)) B atTop (J ×ˢ univ) := by
  let U (i : ℕ) := J ×ˢ g0.metric.ball 0 ((i : ℝ) + 1)
  have hU (i : ℕ) : IsOpen (U i) := by
    dsimp only [U]
    rw [M36.standard_ball_eq_euclidean g0 (by positivity : 0 < (i : ℝ) + 1)]
    exact hJ.prod Metric.isOpen_ball
  have hmono : Monotone U := by
    intro i j hij p hp
    refine ⟨hp.1, hp.2.trans_le (ENNReal.ofReal_le_ofReal ?_)⟩
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    linarith only [hij']
  obtain ⟨sigma, hsigma, B, hB⟩ := exists_rescaled_coordinate_limit hU hmono f
    (fun i => hsmooth ((i : ℝ) + 1) (by positivity))
    (fun i K hK hKU m => hbound ((i : ℝ) + 1) (by positivity) K hK hKU m)
  refine ⟨sigma, hsigma, B, ?_⟩
  simpa only [U, standard_spacetime_buffers_exhaust] using hB

end PoincareConjecture.M44
