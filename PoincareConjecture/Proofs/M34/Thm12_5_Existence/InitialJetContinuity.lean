import PoincareConjecture.Proofs.M34.Thm12_5_Existence.InteriorLimitMetricBounds
import PoincareConjecture.Proofs.M34.Mathlib.InitialModulusContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.InteriorCoefficientLimit

open SpacetimeBounds

variable {g0 : StandardInitialMetric} {A : CompactCapApproximation g0}
  (G : InteriorCoefficientLimit A)

noncomputable def closedCoefficients (p : ℝ × StandardCapSpace) : MetricCoefficient 3 :=
  if p.1 ∈ Ioo 0 A.time then G.coefficients p else g0.metric.euclideanCoefficients p.2

theorem closedCoefficients_of_mem {t : ℝ} (ht : t ∈ Ioo 0 A.time) (x : StandardCapSpace) :
    G.closedCoefficients (t, x) = G.coefficients (t, x) := by
  simp only [closedCoefficients, ht, if_true]

theorem closedCoefficients_zero (x : StandardCapSpace) :
    G.closedCoefficients (0, x) = g0.metric.euclideanCoefficients x := by
  simp [closedCoefficients]

noncomputable def closedSpatialJet (m : ℕ) (p : ℝ × StandardCapSpace) :
    StandardCapSpace [×m]→L[ℝ] MetricCoefficient 3 :=
  iteratedFDeriv ℝ m (fun y => G.closedCoefficients (p.1, y)) p.2

theorem closedSpatialJet_of_mem (m : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 A.time)
    (x : StandardCapSpace) :
    G.closedSpatialJet m (t, x) =
      iteratedFDeriv ℝ m (fun y => G.coefficients (t, y)) x := by
  simp only [closedSpatialJet, closedCoefficients, ht, if_true]

theorem closedSpatialJet_zero (m : ℕ) (x : StandardCapSpace) :
    G.closedSpatialJet m (0, x) = iteratedFDeriv ℝ m g0.metric.euclideanCoefficients x := by
  simp only [closedSpatialJet, G.closedCoefficients_zero]

theorem contDiffOn_closedSpatialJet_interior (m : ℕ) :
    ContDiffOn ℝ ∞ (G.closedSpatialJet m) (Ioo 0 A.time ×ˢ univ) := by
  apply (G.smooth.iteratedFDeriv_snd_of_isOpen isOpen_univ m).congr
  intro p hp
  exact G.closedSpatialJet_of_mem m hp.1 p.2

theorem continuousOn_closedSpatialJet (P : RicciFlowCurvatureTheory.{0}) (m : ℕ) :
    ContinuousOn (G.closedSpatialJet m) (Ico 0 A.time ×ˢ univ) := by
  rintro ⟨t, x⟩ ⟨ht, _hx⟩
  by_cases htzero : t = 0
  · subst t
    obtain ⟨C, _hC, hbound⟩ := G.exists_compact_initial_modulus P
      (isCompact_closedBall x 1) m
    apply continuousWithinAt_zero_of_initial_norm_bound
      (K := Metric.closedBall x 1) (C := C)
      (Metric.closedBall_mem_nhds x zero_lt_one)
      ((g0.metric.contDiffAt_euclideanCoefficients x).continuousAt_iteratedFDeriv
        (by exact_mod_cast le_top)) (G.closedSpatialJet_zero m x)
    intro s hs y hy
    by_cases hszero : s = 0
    · simp only [hszero, G.closedSpatialJet_zero, sub_self, norm_zero, mul_zero, le_refl]
    · have hspos : s ∈ Ioo 0 A.time := ⟨lt_of_le_of_ne hs.1 (Ne.symm hszero), hs.2⟩
      rw [G.closedSpatialJet_of_mem m hspos]
      exact hbound s hspos y hy
  · have htpos : t ∈ Ioo 0 A.time := ⟨lt_of_le_of_ne ht.1 (Ne.symm htzero), ht.2⟩
    exact ((G.contDiffOn_closedSpatialJet_interior m).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨htpos, mem_univ x⟩)).continuousAt.continuousWithinAt

end PoincareConjecture.M34.InteriorCoefficientLimit
