import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CompactSlices
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Absorption
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact









noncomputable section

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace Poincare.Parabolic.Interior

def nestedSpatialRadius (k : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ (k + 1)

def nestedTimeLower (k : ℕ) : ℝ := 1 / 2 + (1 / 2 : ℝ) ^ (k + 2)

def nestedRadius (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k + 4)

theorem nestedRadius_pos (k : ℕ) : 0 < nestedRadius k := by
  exact pow_pos (by norm_num) _

theorem nestedRadius_le_one (k : ℕ) : nestedRadius k ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem nestedRadius_succ (k : ℕ) : nestedRadius (k + 1) = nestedRadius k / 2 := by
  unfold nestedRadius
  rw [show k + 1 + 4 = (k + 4) + 1 by omega, pow_succ]
  ring

theorem nestedRadius_inverse_sq (k : ℕ) : 1 / nestedRadius k ^ 2 = 256 * (4 : ℝ) ^ k := by
  induction k with
  | zero => norm_num [nestedRadius]
  | succ k ih =>
    rw [nestedRadius_succ, div_pow, div_div_eq_mul_div]
    calc
      _ = 4 * (1 / nestedRadius k ^ 2) := by ring
      _ = 4 * (256 * 4 ^ k) := by rw [ih]
      _ = _ := by rw [pow_succ]; ring

theorem nestedSpatialRadius_nonneg (k : ℕ) : 0 ≤ nestedSpatialRadius k := by
  have h : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact sub_nonneg.mpr h

theorem nestedSpatialRadius_lt_one (k : ℕ) : nestedSpatialRadius k < 1 := by
  have h : 0 < (1 / 2 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
  dsimp [nestedSpatialRadius]
  linarith

theorem nestedTimeLower_ge_half (k : ℕ) : 1 / 2 ≤ nestedTimeLower k := by
  have h : 0 ≤ (1 / 2 : ℝ) ^ (k + 2) := pow_nonneg (by norm_num) _
  dsimp [nestedTimeLower]
  linarith

theorem nestedTimeLower_le_one (k : ℕ) : nestedTimeLower k ≤ 1 := by
  have h : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  dsimp [nestedTimeLower]
  rw [pow_add]
  norm_num
  linarith

theorem nestedSpatialRadius_add_two_radius_le (k : ℕ) :
    nestedSpatialRadius k + 2 * nestedRadius k ≤ nestedSpatialRadius (k + 1) := by
  have h : 0 ≤ (1 / 2 : ℝ) ^ k := pow_nonneg (by norm_num) _
  simp only [nestedSpatialRadius, nestedRadius, pow_add, pow_one]
  norm_num
  linarith

theorem nestedTimeLower_sub_radius_sq_ge (k : ℕ) :
    nestedTimeLower (k + 1) ≤ nestedTimeLower k - nestedRadius k ^ 2 := by
  have hr := nestedRadius_pos k
  have hr1 := nestedRadius_le_one k
  have hgap : nestedTimeLower k - nestedTimeLower (k + 1) = 2 * nestedRadius k := by
    simp only [nestedTimeLower, nestedRadius, pow_add, pow_one]
    norm_num
    ring
  nlinarith

variable {E : Type*} [NormedAddCommGroup E]

def nestedCylinder (k : ℕ) : Set (E × ℝ) :=
  Metric.closedBall 0 (nestedSpatialRadius k) ×ˢ Icc (nestedTimeLower k) 1

def interiorCompactCylinder : Set (E × ℝ) :=
  Metric.closedBall 0 1 ×ˢ Icc (1 / 2 : ℝ) 1

theorem nestedCylinder_zero : nestedCylinder (E := E) 0 =
    Metric.closedBall 0 (1 / 2 : ℝ) ×ˢ Icc (3 / 4 : ℝ) 1 := by
  norm_num [nestedCylinder, nestedSpatialRadius, nestedTimeLower]

theorem interiorCompactCylinder_subset_heat_domain :
    interiorCompactCylinder (E := E) ⊆ Metric.ball 0 2 ×ˢ Ioo (0 : ℝ) 2 := by
  intro p hp
  exact ⟨lt_of_le_of_lt hp.1 (by norm_num : (1 : ℝ) < 2),
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hp.2.1,
    lt_of_le_of_lt hp.2.2 (by norm_num : (1 : ℝ) < 2)⟩

theorem origin_mem_nestedCylinder (k : ℕ) : (0, (1 : ℝ)) ∈ nestedCylinder (E := E) k := by
  exact ⟨by simpa using nestedSpatialRadius_nonneg k, nestedTimeLower_le_one k, le_rfl⟩

theorem nestedCylinder_nonempty (k : ℕ) : (nestedCylinder (E := E) k).Nonempty :=
  ⟨_, origin_mem_nestedCylinder k⟩

theorem nestedCylinder_subset_interiorCompactCylinder (k : ℕ) :
    nestedCylinder (E := E) k ⊆ interiorCompactCylinder := by
  intro p hp
  exact ⟨hp.1.trans (nestedSpatialRadius_lt_one k).le,
    (nestedTimeLower_ge_half k).trans hp.2.1, hp.2.2⟩

theorem mem_nestedCylinder_succ_of_mem_local (k : ℕ) {x y : E} {t s : ℝ}
    (hp : (x, t) ∈ nestedCylinder k)
    (hy : y ∈ Metric.closedBall x (2 * nestedRadius k))
    (hs : s ∈ Icc (t - nestedRadius k ^ 2) t) :
    (y, s) ∈ nestedCylinder (k + 1) := by
  refine ⟨?_, ?_, hs.2.trans hp.2.2⟩
  · calc
      dist y 0 ≤ dist y x + dist x 0 := dist_triangle _ _ _
      _ ≤ 2 * nestedRadius k + nestedSpatialRadius k := add_le_add hy hp.1
      _ ≤ nestedSpatialRadius (k + 1) := by
        simpa only [add_comm] using nestedSpatialRadius_add_two_radius_le k
  · have h := nestedTimeLower_sub_radius_sq_ge k
    linarith [hp.2.1, hs.1]

theorem nestedCylinder_subset_succ (k : ℕ) :
    nestedCylinder (E := E) k ⊆ nestedCylinder (k + 1) := by
  intro p hp
  apply mem_nestedCylinder_succ_of_mem_local k hp
  · simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (nestedRadius_pos k).le
  · exact ⟨sub_le_self _ (sq_nonneg _), le_rfl⟩

theorem isCompact_nestedCylinder [ProperSpace E] (k : ℕ) :
    IsCompact (nestedCylinder (E := E) k) :=
  (isCompact_closedBall _ _).prod isCompact_Icc

theorem isCompact_interiorCompactCylinder [ProperSpace E] :
    IsCompact (interiorCompactCylinder (E := E)) :=
  (isCompact_closedBall _ _).prod isCompact_Icc

variable {F : Type*} [NormedAddCommGroup F]

def nestedJetSup (g : E × ℝ → F) (k : ℕ) : ℝ :=
  sSup ((fun p => ‖g p‖) '' nestedCylinder k)

theorem bddAbove_nestedJet_image [ProperSpace E] {g : E × ℝ → F}
    (hg : ContinuousOn g interiorCompactCylinder) (k : ℕ) :
    BddAbove ((fun p => ‖g p‖) '' nestedCylinder k) :=
  (isCompact_nestedCylinder k).bddAbove_image
    (hg.mono (nestedCylinder_subset_interiorCompactCylinder k)).norm

theorem norm_le_nestedJetSup [ProperSpace E] {g : E × ℝ → F}
    (hg : ContinuousOn g interiorCompactCylinder) {k : ℕ} {p : E × ℝ}
    (hp : p ∈ nestedCylinder k) : ‖g p‖ ≤ nestedJetSup g k :=
  le_csSup (bddAbove_nestedJet_image hg k) (mem_image_of_mem _ hp)

theorem nestedJetSup_nonneg [ProperSpace E] {g : E × ℝ → F}
    (hg : ContinuousOn g interiorCompactCylinder) (k : ℕ) : 0 ≤ nestedJetSup g k :=
  (norm_nonneg _).trans (norm_le_nestedJetSup hg (origin_mem_nestedCylinder k))

theorem nestedJetSup_le {g : E × ℝ → F} {k : ℕ} {M : ℝ}
    (hM : ∀ p ∈ nestedCylinder k, ‖g p‖ ≤ M) : nestedJetSup g k ≤ M := by
  apply csSup_le ((nestedCylinder_nonempty k).image _)
  rintro _ ⟨p, hp, rfl⟩
  exact hM p hp

theorem exists_bound_nestedJetSup [ProperSpace E] {g : E × ℝ → F}
    (hg : ContinuousOn g interiorCompactCylinder) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k, nestedJetSup g k ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_interiorCompactCylinder.bddAbove_image hg.norm
  refine ⟨max 0 M, le_max_left _ _, fun k => nestedJetSup_le fun p hp => ?_⟩
  exact (hM (mem_image_of_mem _ (nestedCylinder_subset_interiorCompactCylinder k hp))).trans
    (le_max_right _ _)

theorem nestedJetSup_mono [ProperSpace E] {g : E × ℝ → F}
    (hg : ContinuousOn g interiorCompactCylinder) (k : ℕ) :
    nestedJetSup g k ≤ nestedJetSup g (k + 1) :=
  nestedJetSup_le fun _ hp => norm_le_nestedJetSup hg (nestedCylinder_subset_succ k hp)

theorem nestedJetSup_zero_le_of_pointwise_recurrence [ProperSpace E]
    {g : E × ℝ → F} (hg : ContinuousOn g interiorCompactCylinder) {A θ : ℝ}
    (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hsmall : θ * 4 < 1)
    (hstep : ∀ k, ∀ p ∈ nestedCylinder k,
      ‖g p‖ ≤ A * (4 : ℝ) ^ k + θ * nestedJetSup g (k + 1)) :
    nestedJetSup g 0 ≤ A / (1 - θ * 4) := by
  obtain ⟨M, _, hM⟩ := exists_bound_nestedJetSup hg
  simpa using le_geometric_bound_of_le_add_mul_succ hA (by norm_num : (1 : ℝ) ≤ 4)
    hθ hsmall hM (fun k => nestedJetSup_le (hstep k)) 0

section Hessian

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [ProperSpace E]

theorem exists_bound_nested_spatial_hessian {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k, nestedJetSup (spatialDerivative (spatialDerivative f)) k ≤ M :=
  exists_bound_nestedJetSup
    (contDiff_spatialDerivative (contDiff_spatialDerivative hf)).continuous.continuousOn

theorem norm_fderiv_fderiv_origin_le_of_nested_recurrence
    {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f) {A θ : ℝ}
    (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hsmall : θ * 4 < 1)
    (hstep : ∀ k, ∀ p ∈ nestedCylinder k,
      ‖spatialDerivative (spatialDerivative f) p‖ ≤
        A * (4 : ℝ) ^ k + θ * nestedJetSup (spatialDerivative (spatialDerivative f)) (k + 1))
    (v w : E) :
    ‖fderiv ℝ (fun y => fderiv ℝ (fun z => f (z, 1)) y) 0 v w‖ ≤
      A / (1 - θ * 4) * ‖v‖ * ‖w‖ := by
  have hc : ContinuousOn (spatialDerivative (spatialDerivative f)) interiorCompactCylinder :=
    (contDiff_spatialDerivative (contDiff_spatialDerivative hf)).continuous.continuousOn
  have hsup := nestedJetSup_zero_le_of_pointwise_recurrence hc hA hθ hsmall hstep
  rw [fderiv_fderiv_spatialSlice hf]
  calc
    _ ≤ ‖spatialDerivative (spatialDerivative f) (0, 1)‖ * ‖v‖ * ‖w‖ :=
      ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ nestedJetSup (spatialDerivative (spatialDerivative f)) 0 * ‖v‖ * ‖w‖ := by
      gcongr
      exact norm_le_nestedJetSup hc (origin_mem_nestedCylinder 0)
    _ ≤ _ := by gcongr

end Hessian

end Poincare.Parabolic.Interior
