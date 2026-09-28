import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.Eventual
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.SourceCharts.Rescaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.NormalChartCover

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

local instance ancientRescaling_sourceTopology (k : ℕ) : TopologicalSpace (S.carrier k).carrier :=
  (S.carrier k).topologicalSpace
local instance ancientRescaling_sourceCharts (k : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (S.carrier k).carrier :=
  (S.carrier k).chartedSpace
local instance ancientRescaling_sourceManifold (k : ℕ) : IsManifold (𝓡 n) ∞ (S.carrier k).carrier :=
  (S.carrier k).isManifold
local instance ancientRescaling_unitBallNonempty :
    Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩

variable {R ρ a b : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k → NormalChartCover ((S.flow k).flow.metric)
      (S.flow k).base T' T ((j : ℝ) + 1) (R j) (ρ j) (a j) (b j) (N j))

theorem diagonalUnitBallMap_eventually_bounded_spacetime_derivatives_on_open
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j) (i : ℕ)
    {W : Set ℝ} (hW : IsOpen W)
    (hsmooth : LocallyEventuallyContDiff
      (W ×ˢ ball (0 : EuclideanSpace ℝ (Fin n)) (ρ (Nat.unpair i).1))
      (fun k (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
        ((S.flow k).flow.metric z.1).pullbackCoefficients
          ((cover k (min (Nat.unpair i).1 k) (min_le_right _ _)).chart
            ⟨(Nat.unpair i).2 % (N (min (Nat.unpair i).1 k) + 1),
              Nat.mod_lt _ (Nat.succ_pos _)⟩) z.2))
    (hraw : ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact K →
      K ⊆ W ×ˢ ball 0 (ρ (Nat.unpair i).1) → ∀ m : ℕ, ∃ B : ℝ,
      ∀ᶠ k in atTop, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((S.flow k).flow.metric z.1).pullbackCoefficients
            ((cover k (min (Nat.unpair i).1 k) (min_le_right _ _)).chart
              ⟨(Nat.unpair i).2 % (N (min (Nat.unpair i).1 k) + 1),
                Nat.mod_lt _ (Nat.succ_pos _)⟩) z.2) z‖ ≤ B) :
    ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact K →
      K ⊆ W ×ˢ ball 0 1 → ∀ m : ℕ, ∃ B : ℝ,
      ∀ᶠ k in atTop, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((S.flow k).flow.metric z.1).pullbackCoefficients
            (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
              (fun _ => isOpen_ball) (i := i) (diagonalUnitBallMap cover k i)) z.2) z‖ ≤ B := by
  let j := (Nat.unpair i).1
  let L : (ℝ × EuclideanSpace ℝ (Fin n)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)) :=
    (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n))).prod
      ((ρ j / 2) • ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n)))
  let rawStage := fun k j (hjk : j ≤ k) (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
    ((S.flow k).flow.metric z.1).pullbackCoefficients
      ((cover k j hjk).chart
        ⟨(Nat.unpair i).2 % (N j + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩) z.2
  let raw := fun k => rawStage k (min j k) (min_le_right _ _)
  have hstage (k : ℕ) (hk : j ≤ k) : raw k = rawStage k j hk := by
    funext z
    simp only [raw, min_eq_left hk]
  have hmap : MapsTo L (W ×ˢ ball 0 1) (W ×ˢ ball 0 (ρ j)) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    exact (ball_subset_ball (half_le_self (hρ j).le))
      (rescale_mem_half_ball (hρ j) ⟨z.2, hz.2⟩)
  have heq (k : ℕ) (hk : j ≤ k) : EqOn
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((S.flow k).flow.metric z.1).pullbackCoefficients
          (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
            (fun _ => isOpen_ball) (i := i) (diagonalUnitBallMap cover k i)) z.2)
      (fun z => (ρ j / 2) ^ 2 • raw k (L z)) (W ×ˢ ball 0 1) := by
    intro z hz
    rw [diagonalUnitBallMap_of_le cover k i hk, hstage k hk]
    ext v w
    exact unitBallMap_pullbackCoefficients (cover k j hk) (hρ j) (hρR j) _ z.1 hz.2 v w
  intro K hK hKU m
  have hLK : IsCompact (L '' K) := hK.image L.continuous
  have hLKU : L '' K ⊆ W ×ˢ ball 0 (ρ j) :=
    image_subset_iff.mpr fun z hz => hmap (hKU hz)
  obtain ⟨B, hB⟩ := hraw (L '' K) hLK hLKU m
  refine ⟨‖(ρ j / 2) ^ 2‖ * (B * ∏ _ : Fin m, ‖L‖), ?_⟩
  filter_upwards [hB, eventually_ge_atTop j, hsmooth (L '' K) hLK hLKU]
    with k hkB hk ⟨V, hV, hLKV, hfd⟩ z hz
  have hrawdiff : ContDiffAt ℝ ∞ (raw k) (L z) :=
    hfd.contDiffAt (hV.mem_nhds (hLKV (mem_image_of_mem L hz)))
  rw [eqOn_iteratedFDeriv_of_isOpen (hW.prod isOpen_ball) (heq k hk) m (hKU hz)]
  have hcomp : ContDiffAt ℝ ∞ (raw k ∘ L) z :=
    hrawdiff.comp z L.contDiff.contDiffAt
  change ‖iteratedFDeriv ℝ m (fun z => (ρ j / 2) ^ 2 • (raw k ∘ L) z) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (i := m) (a := (ρ j / 2) ^ 2)
      (hcomp.of_le (by exact_mod_cast le_top))]
  let : IsBoundedSMul ℝ
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  apply (ContinuousMultilinearMap.opNorm_smul_le _ _).trans
  rw [iteratedFDeriv_comp_continuousLinearMap_of_contDiffAt L hrawdiff m]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact ((iteratedFDeriv ℝ m (raw k) (L z)).norm_compContinuousLinearMap_le
    (fun _ : Fin m => L)).trans
      (mul_le_mul_of_nonneg_right (hkB (L z) (mem_image_of_mem L hz))
        (Finset.prod_nonneg fun _ _ => norm_nonneg _))

theorem diagonalUnitBallMap_eventually_lower_coefficients_of_raw
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j) (i : ℕ) (t : ℝ)
    (hraw : ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (ρ (Nat.unpair i).1), ∀ v,
        c * ‖v‖ ^ 2 ≤ ((S.flow k).flow.metric t).pullbackCoefficients
          ((cover k (min (Nat.unpair i).1 k) (min_le_right _ _)).chart
            ⟨(Nat.unpair i).2 % (N (min (Nat.unpair i).1 k) + 1),
              Nat.mod_lt _ (Nat.succ_pos _)⟩) x v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, ∀ v,
        c * ‖v‖ ^ 2 ≤ ((S.flow k).flow.metric t).pullbackCoefficients
          (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
            (fun _ => isOpen_ball) (i := i) (diagonalUnitBallMap cover k i)) x v v := by
  let j := (Nat.unpair i).1
  let rawStage := fun k l (hlk : l ≤ k) (x : EuclideanSpace ℝ (Fin n)) =>
    ((S.flow k).flow.metric t).pullbackCoefficients
      ((cover k l hlk).chart
        ⟨(Nat.unpair i).2 % (N l + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩) x
  obtain ⟨c, hc, hbound⟩ := hraw
  refine ⟨c * (ρ j / 2) ^ 2, mul_pos hc (sq_pos_of_pos (half_pos (hρ j))), ?_⟩
  filter_upwards [hbound, eventually_ge_atTop j] with k hk hkstage x hx v
  have hxraw : (ρ j / 2) • x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (ρ j) :=
    (ball_subset_ball (half_le_self (hρ j).le)) (rescale_mem_half_ball (hρ j) ⟨x, hx⟩)
  have hlower := hk ((ρ j / 2) • x) hxraw v
  rw [diagonalUnitBallMap_of_le cover k i hkstage]
  change c * ‖v‖ ^ 2 ≤ rawStage k (min j k) (min_le_right _ _) ((ρ j / 2) • x) v v
    at hlower
  simp only [min_eq_left hkstage] at hlower
  have hmul := mul_le_mul_of_nonneg_left hlower (sq_nonneg (ρ j / 2))
  have hcoeff := unitBallMap_pullbackCoefficients (cover k j hkstage) (hρ j) (hρR j)
    ⟨(Nat.unpair i).2 % (N j + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩ t hx v v
  convert hmul.trans_eq hcoeff.symm using 1 <;> first | rfl | ring

end PoincareConjecture.NormalChartCover
