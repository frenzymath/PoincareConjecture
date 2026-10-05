import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Metric.TerminalMetric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.InitialModulusContinuity

/-!
# Continuous spatial jets after reversing time at the terminal slice

Time reflection turns the terminal limit into an included initial
boundary. The compact terminal moduli prove joint continuity of every
actual spatial jet there. Only the coefficients are reflected; the
result is not asserted to be a forward Ricci flow. This is the endpoint
regularity step for Morgan-Tian Theorem 12.5, pp. 296-297.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Spatial jets take values in iterated multilinear maps of bilinear forms.
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

/-- The actual Euclidean coefficients of a partial flow are jointly
smooth through its included initial time (Theorem 12.5, pp. 296-297). -/
theorem partialFlow_contDiffOn_coefficients {g0 : StandardInitialMetric}
    (F : PartialStandardCapFlow g0) :
    ContDiffOn ℝ ∞ (fun p : ℝ × StandardCapSpace =>
      (F.flow.metric p.1).euclideanCoefficients p.2) (Ico 0 F.lifetime ×ˢ univ) := by
  simpa only [RiemannianMetric.pullbackCoefficients_id] using
    F.flow.smooth.contDiffOn_spacetime_pullbackCoefficients
      isOpen_univ (contMDiffOn_id (I := 𝓡 3))

namespace PartialFlowTerminalJets

open SpacetimeBounds

variable {g0 : StandardInitialMetric} {F : PartialStandardCapFlow g0} {S : ℝ}
  (L : PartialFlowTerminalJets F S)

/-- Reverse the old coefficients at the terminal time, with the actual
terminal field at nonpositive reflected times (Theorem 12.5, pp. 296-297). -/
noncomputable def reverseCoefficients (p : ℝ × StandardCapSpace) : MetricCoefficient 3 :=
  if 0 < p.1 then (F.flow.metric (S - p.1)).euclideanCoefficients p.2
  else L.coefficients p.2

/-- Positive reflected times are the old metric coefficients at the
corresponding earlier times (Theorem 12.5, pp. 296-297). -/
theorem reverseCoefficients_of_pos {t : ℝ} (ht : 0 < t) (x : StandardCapSpace) :
    L.reverseCoefficients (t, x) = (F.flow.metric (S - t)).euclideanCoefficients x := by
  simp only [reverseCoefficients, ht, if_true]

/-- The reflected time-zero slice is exactly the terminal field
(Theorem 12.5, pp. 296-297). -/
theorem reverseCoefficients_zero (x : StandardCapSpace) :
    L.reverseCoefficients (0, x) = L.coefficients x := by
  simp only [reverseCoefficients, lt_self_iff_false, if_false]

/-- Actual spatial derivatives of the reflected coefficient family
(Theorem 12.5, pp. 296-297). -/
noncomputable def reverseSpatialJet (m : ℕ) (p : ℝ × StandardCapSpace) :
    StandardCapSpace [×m]→L[ℝ] MetricCoefficient 3 :=
  iteratedFDeriv ℝ m (fun x => L.reverseCoefficients (p.1, x)) p.2

/-- At positive reflected times the spatial derivatives are exactly the
old spatial jets (Theorem 12.5, pp. 296-297). -/
theorem reverseSpatialJet_of_pos (m : ℕ) {t : ℝ} (ht : 0 < t) (x : StandardCapSpace) :
    L.reverseSpatialJet m (t, x) =
      iteratedFDeriv ℝ m (F.flow.metric (S - t)).euclideanCoefficients x := by
  simp only [reverseSpatialJet, L.reverseCoefficients_of_pos ht]

/-- At reflected time zero the jets are the actual terminal spatial
derivatives (Theorem 12.5, pp. 296-297). -/
theorem reverseSpatialJet_zero (m : ℕ) (x : StandardCapSpace) :
    L.reverseSpatialJet m (0, x) = iteratedFDeriv ℝ m L.coefficients x := by
  simp only [reverseSpatialJet, L.reverseCoefficients_zero]

/-- Time reflection preserves interior joint smoothness of the old
coefficient family (Theorem 12.5, pp. 296-297). -/
theorem contDiffOn_reverseCoefficients_interior (hSF : S ≤ F.lifetime) :
    ContDiffOn ℝ ∞ L.reverseCoefficients (Ioo 0 S ×ˢ univ) := by
  have hpath : ContDiff ℝ ∞ (fun p : ℝ × StandardCapSpace => (S - p.1, p.2)) := by
    fun_prop
  have hmaps : MapsTo (fun p : ℝ × StandardCapSpace => (S - p.1, p.2))
      (Ioo 0 S ×ˢ univ) (Ico 0 F.lifetime ×ˢ univ) := by
    intro p hp
    exact ⟨⟨sub_nonneg.mpr hp.1.2.le, (sub_lt_self S hp.1.1).trans_le hSF⟩, mem_univ _⟩
  apply ((partialFlow_contDiffOn_coefficients F).comp hpath.contDiffOn hmaps).congr
  intro p hp
  exact L.reverseCoefficients_of_pos hp.1.1 p.2

/-- Every reflected spatial jet is jointly smooth at interior reflected
times (Theorem 12.5, pp. 296-297). -/
theorem contDiffOn_reverseSpatialJet_interior (hSF : S ≤ F.lifetime) (m : ℕ) :
    ContDiffOn ℝ ∞ (L.reverseSpatialJet m) (Ioo 0 S ×ˢ univ) :=
  (L.contDiffOn_reverseCoefficients_interior hSF).iteratedFDeriv_snd_of_isOpen isOpen_univ m

/-- All actual reflected spatial jets are jointly continuous through
the included terminal slice (Theorem 12.5, pp. 296-297). -/
theorem continuousOn_reverseSpatialJet (P : RicciFlowCurvatureTheory.{0})
    (E0 : StandardCapEstimate g0) {B : ℝ} (hS : 0 < S)
    (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B) (m : ℕ) :
    ContinuousOn (L.reverseSpatialJet m) (Ico 0 S ×ˢ univ) := by
  rintro ⟨t, x⟩ ⟨ht, _hx⟩
  by_cases htzero : t = 0
  · subst t
    obtain ⟨D, _hD, hmod⟩ := L.exists_compact_terminal_modulus P E0 hS hSF hB hfull
      (isCompact_closedBall x 1) m
    have hcont := (L.contDiff_coefficients P E0 hS hSF hB hfull).continuous_iteratedFDeriv
      (m := m) (by exact_mod_cast le_top)
    apply continuousWithinAt_zero_of_initial_norm_bound
      (K := Metric.closedBall x 1) (C := D) (Metric.closedBall_mem_nhds x zero_lt_one)
      hcont.continuousAt (L.reverseSpatialJet_zero m x)
    intro r hr y hy
    by_cases hrzero : r = 0
    · simp only [hrzero, L.reverseSpatialJet_zero, sub_self, norm_zero, mul_zero, le_refl]
    · have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hrzero)
      rw [L.reverseSpatialJet_of_pos m hrpos,
        ← L.jet_eq_iteratedFDeriv P E0 hS hSF hB hfull m y]
      have h := hmod (S - r) ⟨sub_nonneg.mpr hr.2.le, sub_lt_self S hrpos⟩ y hy
      simpa only [sub_sub_cancel] using h
  · have htpos : t ∈ Ioo 0 S := ⟨lt_of_le_of_ne ht.1 (Ne.symm htzero), ht.2⟩
    exact ((L.contDiffOn_reverseSpatialJet_interior hSF m).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨htpos, mem_univ x⟩)).continuousAt.continuousWithinAt

end PartialFlowTerminalJets
end PoincareMT.M34
