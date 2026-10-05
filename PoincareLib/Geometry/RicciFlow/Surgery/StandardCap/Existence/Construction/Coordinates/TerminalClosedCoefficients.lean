import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Flow.TerminalEvolution

/-!
# Closing the coefficient family at its terminal time

Reflecting the smooth reversed family back gives left smoothness and
the original-sign equation at the terminal boundary. Locality combines
this with the old initial-endpoint smoothness on the entire closed
slab. This is Morgan-Tian Theorem 12.5, pp. 296-297.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Finite spatial jets and coefficient derivatives have nested map targets.
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34.PartialFlowTerminalJets

open SpacetimeBounds SpacetimeBounds.Bootstrap

variable {g0 : StandardInitialMetric} {F : PartialStandardCapFlow g0} {S : ℝ}
  (L : PartialFlowTerminalJets F S)

/-- The old coefficient field extended by its genuine terminal value
at and beyond the terminal time (Theorem 12.5, pp. 296-297). -/
noncomputable def closedCoefficients (p : ℝ × StandardCapSpace) : MetricCoefficient 3 :=
  L.reverseCoefficients (S - p.1, p.2)

/-- Every time strictly below the terminal time keeps the old coefficient
field exactly (Theorem 12.5, pp. 296-297). -/
theorem closedCoefficients_of_lt {t : ℝ} (ht : t < S) (x : StandardCapSpace) :
    L.closedCoefficients (t, x) = (F.flow.metric t).euclideanCoefficients x := by
  rw [closedCoefficients, L.reverseCoefficients_of_pos (sub_pos.mpr ht), sub_sub_cancel]

/-- At and above the terminal time the coefficients are the terminal
field (Theorem 12.5, pp. 296-297). -/
theorem closedCoefficients_of_le {t : ℝ} (ht : S ≤ t) (x : StandardCapSpace) :
    L.closedCoefficients (t, x) = L.coefficients x := by
  simp only [closedCoefficients, reverseCoefficients, not_lt.mpr (sub_nonpos.mpr ht), if_false]

set_option synthInstance.maxHeartbeats 100000 in
-- Reflection changes only the parameter and leaves all spatial derivatives fixed.
/-- Finite jets of the closed field are the reflected finite jets
(Theorem 12.5, pp. 296-297). -/
theorem closedFiniteSpatialJet (m : ℕ) (t : ℝ) (x : StandardCapSpace) :
    spatialJet m L.closedCoefficients (t, x) =
      spatialJet m L.reverseCoefficients (S - t, x) := rfl

variable (P : RicciFlowCurvatureTheory.{0}) (E0 : StandardCapEstimate g0)
  {B : ℝ} (hS : 0 < S) (hSF : S ≤ F.lifetime) (hB : 0 < B)
  (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
    (F.flow.connection t).curvatureTensorNorm x ≤ B)

include P E0 hS hSF hB hfull

/-- The extended coefficients are jointly smooth on the slab with its
terminal endpoint included (Theorem 12.5, pp. 296-297). -/
theorem contDiffOn_closedCoefficients_Ioc :
    ContDiffOn ℝ ∞ L.closedCoefficients (Ioc 0 S ×ˢ univ) := by
  have hpath : ContDiff ℝ ∞ (fun p : ℝ × StandardCapSpace => (S - p.1, p.2)) := by
    fun_prop
  apply (L.contDiffOn_reverseCoefficients P E0 hS hSF hB hfull).comp hpath.contDiffOn
  intro p hp
  exact ⟨⟨sub_nonneg.mpr hp.1.2, sub_lt_self S hp.1.1⟩, mem_univ _⟩

/-- Initial locality and terminal reflection give joint smoothness on
the full closed time slab (Theorem 12.5, pp. 296-297). -/
theorem contDiffOn_closedCoefficients :
    ContDiffOn ℝ ∞ L.closedCoefficients (Icc 0 S ×ˢ univ) := by
  intro p hp
  by_cases ht : p.1 < S
  · have hnear : {q : ℝ × StandardCapSpace | q.1 < S} ∈ 𝓝[Icc 0 S ×ˢ univ] p :=
      mem_nhdsWithin_of_mem_nhds ((isOpen_Iio.preimage continuous_fst).mem_nhds ht)
    have hprod : Ico 0 F.lifetime ×ˢ (univ : Set StandardCapSpace) ∈
        𝓝[Icc 0 S ×ˢ univ] p := by
      filter_upwards [self_mem_nhdsWithin, hnear] with q hq hqt
      exact ⟨⟨hq.1.1, hqt.trans_le hSF⟩, mem_univ _⟩
    have hreg := ((partialFlow_contDiffOn_coefficients F) p
      ⟨⟨hp.1.1, ht.trans_le hSF⟩, mem_univ _⟩).mono_of_mem_nhdsWithin hprod
    apply hreg.congr_of_eventuallyEq_of_mem _ hp
    filter_upwards [hnear] with q hq
    exact L.closedCoefficients_of_lt hq q.2
  · have hpos : 0 < p.1 := hS.trans_le (not_lt.mp ht)
    have hnear : {q : ℝ × StandardCapSpace | 0 < q.1} ∈ 𝓝[Icc 0 S ×ˢ univ] p :=
      mem_nhdsWithin_of_mem_nhds ((isOpen_Ioi.preimage continuous_fst).mem_nhds hpos)
    have hprod : Ioc 0 S ×ˢ (univ : Set StandardCapSpace) ∈
        𝓝[Icc 0 S ×ˢ univ] p := by
      filter_upwards [self_mem_nhdsWithin, hnear] with q hq hqt
      exact ⟨⟨hqt, hq.1.2⟩, mem_univ _⟩
    exact ((L.contDiffOn_closedCoefficients_Ioc P E0 hS hSF hB hfull) p
      ⟨⟨hpos, hp.1.2⟩, mem_univ _⟩).mono_of_mem_nhdsWithin hprod

set_option synthInstance.maxHeartbeats 100000 in
-- The two time reflections cancel their negative derivative signs.
/-- On the terminally closed positive slab the actual within-time
derivative is the original-sign Ricci operator (Theorem 12.5, pp. 296-297). -/
theorem hasDerivWithinAt_closedCoefficients_Ioc {t : ℝ} (ht : t ∈ Ioc 0 S)
    (x : StandardCapSpace) :
    HasDerivWithinAt (fun s => L.closedCoefficients (s, x))
      (jetRicciFlowOperator 3 (spatialJet 2 L.closedCoefficients (t, x))) (Ioc 0 S) t := by
  have hr : S - t ∈ Ico 0 S := ⟨sub_nonneg.mpr ht.2, sub_lt_self S ht.1⟩
  have hd := L.hasDerivWithinAt_reverseCoefficients P E0 hS hSF hB hfull hr x
  have hpath : HasDerivWithinAt (fun s : ℝ => S - s) (-1) (Ioc 0 S) t := by
    convert! (hasDerivWithinAt_id t (Ioc 0 S)).const_sub S using 1
  have hmaps : MapsTo (fun s : ℝ => S - s) (Ioc 0 S) (Ico 0 S) :=
    fun _ hs => ⟨sub_nonneg.mpr hs.2, sub_lt_self S hs.1⟩
  have h := hd.scomp t hpath hmaps
  simp only [neg_smul, one_smul, neg_neg] at h
  convert! h using 1

end PoincareMT.M34.PartialFlowTerminalJets
