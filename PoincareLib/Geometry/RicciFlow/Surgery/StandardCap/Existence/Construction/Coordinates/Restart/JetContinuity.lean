import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Metric.Restart.MetricBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.InitialModulusContinuity

/-!
# Metric-general Initial values and joint continuity of every spatial jet

At time zero the coefficient field is defined to be the prescribed
metric. Its actual spatial derivatives agree with the extended interior
jets. Their compact-uniform initial moduli prove joint continuity on the
included initial slab. This is Morgan-Tian Theorem 12.5, p. 297.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34.MetricInteriorCoefficientLimit

open SpacetimeBounds

variable {ginit : RiemannianMetric 3 StandardCapSpace} {Mfamily : ℕ → Type}
  [∀ k, TopologicalSpace (Mfamily k)] [∀ k, ChartedSpace StandardCapSpace (Mfamily k)]
  [∀ k, IsManifold (𝓡 3) ∞ (Mfamily k)]
  {A : MetricFlowApproximation ginit Mfamily}
  (G : MetricInteriorCoefficientLimit A)

/-- Extend the coefficient field by the exact initial metric outside the
open interior time domain (Theorem 12.5, p. 297). -/
noncomputable def closedCoefficients (p : ℝ × StandardCapSpace) : MetricCoefficient 3 :=
  if p.1 ∈ Ioo 0 A.time then G.coefficients p else ginit.euclideanCoefficients p.2

/-- The extended field agrees with the smooth interior limit at positive
interior times (Theorem 12.5, p. 297). -/
theorem closedCoefficients_of_mem {t : ℝ} (ht : t ∈ Ioo 0 A.time) (x : StandardCapSpace) :
    G.closedCoefficients (t, x) = G.coefficients (t, x) := by
  simp only [closedCoefficients, ht, if_true]

/-- The time-zero coefficients are exactly the prescribed initial metric
(Theorem 12.5, p. 297). -/
theorem closedCoefficients_zero (x : StandardCapSpace) :
    G.closedCoefficients (0, x) = ginit.euclideanCoefficients x := by
  simp [closedCoefficients]

/-- Actual spatial derivatives of the extended coefficient field
(Theorem 12.5, p. 297). -/
noncomputable def closedSpatialJet (m : ℕ) (p : ℝ × StandardCapSpace) :
    StandardCapSpace [×m]→L[ℝ] MetricCoefficient 3 :=
  iteratedFDeriv ℝ m (fun y => G.closedCoefficients (p.1, y)) p.2

/-- At positive times these are the spatial jets of the interior limit
(Theorem 12.5, p. 297). -/
theorem closedSpatialJet_of_mem (m : ℕ) {t : ℝ} (ht : t ∈ Ioo 0 A.time)
    (x : StandardCapSpace) :
    G.closedSpatialJet m (t, x) =
      iteratedFDeriv ℝ m (fun y => G.coefficients (t, y)) x := by
  simp only [closedSpatialJet, closedCoefficients, ht, if_true]

/-- Every time-zero spatial jet is the actual initial metric jet
(Theorem 12.5, p. 297). -/
theorem closedSpatialJet_zero (m : ℕ) (x : StandardCapSpace) :
    G.closedSpatialJet m (0, x) = iteratedFDeriv ℝ m ginit.euclideanCoefficients x := by
  simp only [closedSpatialJet, G.closedCoefficients_zero]

/-- The extended spatial jets remain jointly smooth at interior times
(Theorem 12.5, p. 297). -/
theorem contDiffOn_closedSpatialJet_interior (m : ℕ) :
    ContDiffOn ℝ ∞ (G.closedSpatialJet m) (Ioo 0 A.time ×ˢ univ) := by
  apply (G.smooth.iteratedFDeriv_snd_of_isOpen isOpen_univ m).congr
  intro p hp
  exact G.closedSpatialJet_of_mem m hp.1 p.2

/-- Every actual spatial jet is jointly continuous through time zero
(Theorem 12.5, p. 297). -/
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
      ((ginit.contDiffAt_euclideanCoefficients x).continuousAt_iteratedFDeriv
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

end PoincareMT.M34.MetricInteriorCoefficientLimit
