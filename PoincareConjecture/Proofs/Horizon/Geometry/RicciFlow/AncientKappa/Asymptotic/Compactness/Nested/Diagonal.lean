import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Nested.ChartTests
import PoincareConjecture.Proofs.Horizon.Topology.Sequences.UniformDiagonal







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientRescalingSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] {K : AncientKappaSolution n M}

theorem nestedWindowLimit_subsequence_succ_le (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j k : ℕ) :
    (S.nestedWindowLimit P j).geometric_limit.subsequence k ≤
      (S.nestedWindowLimit P (j + 1)).geometric_limit.subsequence k := by
  change (S.nestedWindowLimit P j).geometric_limit.subsequence k ≤
    (S.chosenWindowExtension P j (S.nestedWindowLimit P j)).next.geometric_limit.subsequence k
  rw [(S.chosenWindowExtension P j (S.nestedWindowLimit P j)).subsequence_eq]
  exact (S.nestedWindowLimit P j).geometric_limit.subsequence_strictMono.monotone
    ((S.chosenWindowExtension P j (S.nestedWindowLimit P j)).refinement_strictMono.id_le k)

theorem nestedWindowLimit_diagonal_strictMono (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    StrictMono (fun j => (S.nestedWindowLimit P j).geometric_limit.subsequence (σ j)) := by
  apply strictMono_nat_of_lt_succ
  intro j
  exact ((S.nestedWindowLimit P j).geometric_limit.subsequence_strictMono
    (hσ (Nat.lt_succ_self j))).trans_le (S.nestedWindowLimit_subsequence_succ_le P j (σ (j + 1)))

theorem exists_nested_spatial_diagonal (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K)
    (T : (S.nestedWindowLimit P 0).geometric_limit.limitCarrier.CompactChartTests) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ j, S.initialWindowIdentification P j ''
        closure ((S.nestedWindowLimit P 0).geometric_limit.exhaustion j) ⊆
          (S.nestedWindowLimit P j).geometric_limit.exhaustion (σ j)) ∧
      ∀ i m r, TendstoUniformlyOn
        (fun j => iteratedFDeriv ℝ r (S.nestedSpatialCoefficients P (T.center i) j (σ j)))
        (iteratedFDeriv ℝ r (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((S.gluedShiftedAncientFlow P).metric z.1).pullbackCoefficients
            (extChartAt (𝓡 n) (T.center i)).symm z.2)) atTop (T.compact i m) := by
  classical
  let A (i j : ℕ) : Set (ℝ × EuclideanSpace ℝ (Fin n)) :=
    if T.compact i.unpair.1 i.unpair.2.unpair.1 ⊆ shiftedCompactnessWindow j ×ˢ
        (extChartAt (𝓡 n) (T.center i.unpair.1)).target
      then T.compact i.unpair.1 i.unpair.2.unpair.1 else ∅
  have hAmono (i : ℕ) : Monotone (A i) := by
    intro j k hjk
    dsimp only [A]
    split_ifs with hj hk hk
    · exact Subset.rfl
    · exact False.elim (hk (hj.trans (prod_mono (shiftedCompactnessWindow_mono hjk) Subset.rfl)))
    · exact empty_subset _
    · exact Subset.rfl
  have hAcompact (i j : ℕ) : IsCompact (A i j) := by
    dsimp only [A]
    split_ifs
    · exact T.isCompact _ _
    · exact isCompact_empty
  have hAsubset (i j : ℕ) : A i j ⊆ shiftedCompactnessWindow j ×ˢ
      (extChartAt (𝓡 n) (T.center i.unpair.1)).target := by
    dsimp only [A]
    split_ifs with h
    · exact h
    · exact empty_subset _
  let side (j k : ℕ) := S.initialWindowIdentification P j ''
    closure ((S.nestedWindowLimit P 0).geometric_limit.exhaustion j) ⊆
      (S.nestedWindowLimit P j).geometric_limit.exhaustion k
  have hside (j : ℕ) : ∀ᶠ k in atTop, side j k := by
    obtain ⟨s, hs⟩ := (S.nestedWindowLimit P j).geometric_limit.exists_exhaustion_superset
      (((S.nestedWindowLimit P 0).geometric_limit.exhaustion_compactClosure j).image
        (S.initialWindowIdentification P j).continuous)
    filter_upwards [eventually_ge_atTop s] with k hk
    exact hs.trans ((S.nestedWindowLimit P j).geometric_limit.exhaustion_monotone hk)
  obtain ⟨σ, hσ, hσside, hσjet⟩ := Poincare.exists_strictMono_tendstoUniformlyOn_diagonal
    (fun i j k => iteratedFDeriv ℝ i.unpair.2.unpair.2
      (S.nestedSpatialCoefficients P (T.center i.unpair.1) j k))
    (fun i => iteratedFDeriv ℝ i.unpair.2.unpair.2
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((S.gluedShiftedAncientFlow P).metric z.1).pullbackCoefficients
          (extChartAt (𝓡 n) (T.center i.unpair.1)).symm z.2))
    A hAmono (fun j i _ => S.tendstoUniformlyOn_nestedSpatialCoefficients_jets P j
      (T.center i.unpair.1) i.unpair.2.unpair.2 (hAcompact i j) (hAsubset i j)) hside
  refine ⟨σ, hσ, hσside, fun i m r => ?_⟩
  obtain ⟨l, hl⟩ := exists_compact_subset_shiftedCompactnessWindow
    ((T.isCompact i m).image continuous_fst)
    (by rintro t ⟨z, hz, rfl⟩; exact (T.subset i m hz).1)
  have hdom : T.compact i m ⊆ shiftedCompactnessWindow l ×ˢ
      (extChartAt (𝓡 n) (T.center i)).target :=
    fun z hz => ⟨hl (mem_image_of_mem _ hz), (T.subset i m hz).2⟩
  have hh := hσjet (Nat.pair i (Nat.pair m r)) l
  have hr : (Nat.unpair (Nat.unpair (Nat.pair i (Nat.pair m r))).2).2 = r := by simp
  rw [hr] at hh
  simpa only [A, Nat.unpair_pair, if_pos hdom] using hh

end PoincareConjecture.AncientRescalingSequence
