import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandPhysicalSeparator
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandEndpointGeometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface

namespace PoincareConjecture

theorem m64Intrinsic_exists_joined_band_outer_separators
    (L R : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {f g : ℝ → ℝ} {a b ua wa ub wb ra rb s t us ws ut wt rs rt : ℝ}
    (hab : a < b) (hst : s < t)
    (B : ObliqueBandFaces
      (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
      f a b ua wa ub wb ra rb)
    (C : ObliqueBandFaces
      (collarParameterEquiv.trans R).toHomeomorph.toOpenPartialHomeomorph
      g s t us ws ut wt rs rt)
    (hinter : B.carrier ∩ C.carrier = B.rightCut) (hshared : B.rightCut = C.leftCut)
    {vA dA vB dB : AnnulusCoordinates}
    (hdirA : L (ua, wa) = dA) (hdirB : R (ut, wt) = dB)
    (htangentA : ∃ speed : ℝ, 0 < speed ∧ vA = speed • L (1, deriv f a))
    (htangentB : ∃ speed : ℝ, 0 < speed ∧ vB = speed • R (1, deriv g t))
    (htransA : 0 < inner ℝ (quarterTurn vA) dA)
    (htransB : 0 < inner ℝ (quarterTurn vB) dB) :
    ∃ (ellA ellB : AnnulusCoordinates →L[ℝ] ℝ) (WA WB : Set AnnulusCoordinates),
      IsOpen WA ∧ IsOpen WB ∧ L (a, f a) ∈ WA ∧ R (t, g t) ∈ WB ∧
      ellA dA = 0 ∧ ellB dB = 0 ∧ ellA vA < 0 ∧ 0 < ellB vB ∧
      (∀ z ∈ (B.carrier ∪ C.carrier) ∩ WA, ellA (z - L (a, f a)) ≤ 0) ∧
      ∀ z ∈ (B.carrier ∪ C.carrier) ∩ WB, ellB (z - R (t, g t)) ≤ 0 := by
  obtain ⟨ellA, WA, hWA, hpA, hkerA, hsignA, hsepA⟩ :=
    m64Intrinsic_exists_band_physical_separator L hab B false hdirA htangentA htransA
  obtain ⟨ellB, WB, hWB, hpB, hkerB, hsignB, hsepB⟩ :=
    m64Intrinsic_exists_band_physical_separator R hst C true hdirB htangentB htransB
  have hmemA : L (a, f a) ∈ B.carrier := by
    rw [← m64Intrinsic_band_left_endpoint_zero L B]
    exact B.isClosed_carrier.frontier_subset
      (B.endpointEdge_subset_frontier false ⟨0, by norm_num, rfl⟩)
  have hmemB : R (t, g t) ∈ C.carrier := by
    rw [← m64Intrinsic_band_right_endpoint_zero R C]
    exact C.isClosed_carrier.frontier_subset
      (C.endpointEdge_subset_frontier true ⟨0, by norm_num, rfl⟩)
  have havoidA : L (a, f a) ∉ C.carrier := by
    intro h
    have hcut : L (a, f a) ∈ B.rightCut := hinter ▸ And.intro hmemA h
    apply m64Intrinsic_band_endpoint_zero_not_opposite B false
    simpa only [m64Intrinsic_band_left_endpoint_zero, Bool.false_eq_true, ↓reduceIte] using hcut
  have havoidB : R (t, g t) ∉ B.carrier := by
    intro h
    have hcut : R (t, g t) ∈ B.rightCut := hinter ▸ And.intro h hmemB
    rw [hshared] at hcut
    apply m64Intrinsic_band_endpoint_zero_not_opposite C true
    simpa only [m64Intrinsic_band_right_endpoint_zero, ↓reduceIte] using hcut
  refine ⟨ellA, ellB, WA ∩ C.carrierᶜ, WB ∩ B.carrierᶜ,
    hWA.inter C.isClosed_carrier.isOpen_compl, hWB.inter B.isClosed_carrier.isOpen_compl,
    ⟨hpA, havoidA⟩, ⟨hpB, havoidB⟩, hkerA, hkerB, hsignA, hsignB, ?_, ?_⟩
  · rintro z ⟨hzB | hzC, hzW, hznot⟩
    · exact hsepA z ⟨hzB, hzW⟩
    · exact (hznot hzC).elim
  · rintro z ⟨hzB | hzC, hzW, hznot⟩
    · exact (hznot hzB).elim
    · exact hsepB z ⟨hzC, hzW⟩

end PoincareConjecture
