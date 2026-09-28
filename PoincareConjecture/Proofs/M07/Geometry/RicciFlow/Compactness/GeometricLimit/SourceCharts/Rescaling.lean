import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.SourceCharts.Coefficients
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.PullbackCoefficients
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LinearPrecompose
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.LocalConvergence












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter Metric Poincare.Gluing Poincare.Analysis.Calculus
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.NormalChartCover

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

local instance (k : ℕ) : TopologicalSpace (S.carrier k).carrier :=
  (S.carrier k).topologicalSpace
local instance (k : ℕ) : ChartedSpace (EuclideanSpace ℝ (Fin n)) (S.carrier k).carrier :=
  (S.carrier k).chartedSpace
local instance (k : ℕ) : IsManifold (𝓡 n) ∞ (S.carrier k).carrier :=
  (S.carrier k).isManifold
local instance : Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩

variable {R ρ a b : ℕ → ℝ} {N : ℕ → ℕ}
    (cover : ∀ k j, j ≤ k → NormalChartCover ((S.flow k).flow.metric)
      (S.flow k).base T' T ((j : ℝ) + 1) (R j) (ρ j) (a j) (b j) (N j))



theorem diagonalUnitBallMap_eventually_bounded_spacetime_derivatives
    (hρ : ∀ j, 0 < ρ j) (hρR : ∀ j, ρ j / 2 ≤ R j) (i : ℕ)
    (hraw : ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact K →
      K ⊆ Ioo T' T ×ˢ ball 0 (ρ (Nat.unpair i).1) → ∀ m : ℕ, ∃ B : ℝ,
      ∀ᶠ k in atTop, ∀ z ∈ K,
        ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((S.flow k).flow.metric z.1).pullbackCoefficients
            ((cover k (min (Nat.unpair i).1 k) (min_le_right _ _)).chart
              ⟨(Nat.unpair i).2 % (N (min (Nat.unpair i).1 k) + 1),
                Nat.mod_lt _ (Nat.succ_pos _)⟩) z.2) z‖ ≤ B) :
    ∀ K : Set (ℝ × EuclideanSpace ℝ (Fin n)), IsCompact K →
      K ⊆ Ioo T' T ×ˢ ball 0 1 → ∀ m : ℕ, ∃ B : ℝ,
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
  have hmap : MapsTo L (Ioo T' T ×ˢ ball 0 1) (Ioo T' T ×ˢ ball 0 (ρ j)) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    exact (ball_subset_ball (half_le_self (hρ j).le))
      (rescale_mem_half_ball (hρ j) ⟨z.2, hz.2⟩)
  have heq (k : ℕ) (hk : j ≤ k) : EqOn
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((S.flow k).flow.metric z.1).pullbackCoefficients
          (ChartDistance.chartParametrization (fun _ : ℕ => ball 0 1)
            (fun _ => isOpen_ball) (i := i) (diagonalUnitBallMap cover k i)) z.2)
      (fun z => (ρ j / 2) ^ 2 • raw k (L z)) (Ioo T' T ×ˢ ball 0 1) := by
    intro z hz
    rw [diagonalUnitBallMap_of_le cover k i hk]
    rw [hstage k hk]
    ext v w
    exact unitBallMap_pullbackCoefficients (cover k j hk) (hρ j) (hρR j) _ z.1 hz.2 v w
  have hsmooth (k : ℕ) (hk : j ≤ k) (z : ℝ × EuclideanSpace ℝ (Fin n))
      (hz : z ∈ Ioo T' T ×ˢ ball 0 1) : ContDiffAt ℝ ∞ (raw k) (L z) := by
    rw [hstage k hk]
    apply (S.flow k).flow.smooth.contDiffAt_spacetime_pullbackCoefficients isOpen_Ioo
    · apply (cover k j hk).chart _ |>.contMDiffOn.contMDiffAt
      apply (cover k j hk).chart _ |>.open_source.mem_nhds
      rw [(cover k j hk).source]
      exact (ball_subset_ball (hρR j)) (rescale_mem_half_ball (hρ j) ⟨z.2, hz.2⟩)
    · exact hz.1
  intro K hK hKU m
  obtain ⟨B, hB⟩ := hraw (L '' K) (hK.image L.continuous)
    (image_subset_iff.mpr fun z hz => hmap (hKU hz)) m
  refine ⟨‖(ρ j / 2) ^ 2‖ * (B * ∏ _ : Fin m, ‖L‖), ?_⟩
  filter_upwards [hB, eventually_ge_atTop j] with k hkB hk z hz
  rw [eqOn_iteratedFDeriv_of_isOpen (isOpen_Ioo.prod isOpen_ball) (heq k hk) m (hKU hz)]
  have hcomp : ContDiffAt ℝ ∞ (raw k ∘ L) z :=
    (hsmooth k hk z (hKU hz)).comp z L.contDiff.contDiffAt
  change ‖iteratedFDeriv ℝ m (fun z => (ρ j / 2) ^ 2 • (raw k ∘ L) z) z‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (i := m) (a := (ρ j / 2) ^ 2)
      (hcomp.of_le (by exact_mod_cast le_top))]
  let : IsBoundedSMul ℝ
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
  apply (ContinuousMultilinearMap.opNorm_smul_le _ _).trans
  rw [iteratedFDeriv_comp_continuousLinearMap_of_contDiffAt L
      (hsmooth k hk z (hKU hz)) m]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact ((iteratedFDeriv ℝ m (raw k) (L z)).norm_compContinuousLinearMap_le
    (fun _ : Fin m => L)).trans
      (mul_le_mul_of_nonneg_right (hkB (L z) (mem_image_of_mem L hz))
        (Finset.prod_nonneg fun _ _ => norm_nonneg _))

end PoincareConjecture.NormalChartCover
