import PoincareConjecture.Proofs.M34.Thm12_5_Existence.TerminalEvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.PartialFlowTerminalJets

open SpacetimeBounds SpacetimeBounds.Bootstrap

variable {g0 : StandardInitialMetric} {F : PartialStandardCapFlow g0} {S : ℝ}
  (L : PartialFlowTerminalJets F S)

noncomputable def closedCoefficients (p : ℝ × StandardCapSpace) : MetricCoefficient 3 :=
  L.reverseCoefficients (S - p.1, p.2)

theorem closedCoefficients_of_lt {t : ℝ} (ht : t < S) (x : StandardCapSpace) :
    L.closedCoefficients (t, x) = (F.flow.metric t).euclideanCoefficients x := by
  rw [closedCoefficients, L.reverseCoefficients_of_pos (sub_pos.mpr ht), sub_sub_cancel]

theorem closedCoefficients_of_le {t : ℝ} (ht : S ≤ t) (x : StandardCapSpace) :
    L.closedCoefficients (t, x) = L.coefficients x := by
  simp only [closedCoefficients, reverseCoefficients, not_lt.mpr (sub_nonpos.mpr ht), if_false]

set_option synthInstance.maxHeartbeats 100000 in

theorem closedFiniteSpatialJet (m : ℕ) (t : ℝ) (x : StandardCapSpace) :
    spatialJet m L.closedCoefficients (t, x) =
      spatialJet m L.reverseCoefficients (S - t, x) := rfl

variable (P : RicciFlowCurvatureTheory.{0}) (E0 : StandardCapEstimate g0)
  {B : ℝ} (hS : 0 < S) (hSF : S ≤ F.lifetime) (hB : 0 < B)
  (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
    (F.flow.connection t).curvatureTensorNorm x ≤ B)

include P E0 hS hSF hB hfull

theorem contDiffOn_closedCoefficients_Ioc :
    ContDiffOn ℝ ∞ L.closedCoefficients (Ioc 0 S ×ˢ univ) := by
  have hpath : ContDiff ℝ ∞ (fun p : ℝ × StandardCapSpace => (S - p.1, p.2)) := by
    fun_prop
  apply (L.contDiffOn_reverseCoefficients P E0 hS hSF hB hfull).comp hpath.contDiffOn
  intro p hp
  exact ⟨⟨sub_nonneg.mpr hp.1.2, sub_lt_self S hp.1.1⟩, mem_univ _⟩

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

end PoincareConjecture.M34.PartialFlowTerminalJets
