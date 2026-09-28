import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.UpperPairedNormalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.BandAvoidance
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.LabelCount
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Geometry.ProtectedRegion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Replacement.Geometry
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.PairReplacement.SmallFamily



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SaddleLevel SphereSurgeryCoreCap Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}



theorem exists_terminal_upper_family_replacement_of_prepared
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)
    (E F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hEheight : ∀ y, inner Real (M.v : E3) (E y) = inner Real (M.v : E3) y)
    (hEcore : ∀ D ∈ data.ends.caps, EqOn (E ∘ g) g (D.chart '' closedBall (0 : E2) 1))
    (hFband : EqOn F id data.toTerminalSaddleGeometry.modelBand)
    (hFpoint : ∀ q : S2, F (H (data.toTerminalSaddleGeometry.flatten (g q))) =
      data.toTerminalSaddleGeometry.flatten (E (g q)))
    (hgerms : ∀ i, ∃ U : Set E3, IsOpen U ∧
      (fun x => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x)) ''
        sphere (0 : E2) 1 ⊆ U ∧
      (E '' range g) ∩ U =
        (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) ∩ U)
    {c : Real} (_hlc : data.ends.lowerCut < c) (hcu : c < data.ends.upperCut)
    : ∃ K : Set E3, IsCompact K ∧
      ∃ R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, R y = y) ∧
        EqOn R id (data.toTerminalSaddleGeometry.flatten.symm ''
          data.toTerminalSaddleGeometry.modelBand ∪ {y | inner Real (M.v : E3) y ≤ c}) ∧
        ∀ j : data.ends.UpperCutIndex,
          R '' ((E ∘ g) '' terminalEndCap data.ends (.inr j)) =
            data.toTerminalSaddleGeometry.flatten.symm ''
              data.toTerminalSaddleGeometry.modelCaps (data.labels.symm (.inr j)) := by
  classical
  obtain ⟨r, δ, hr, hδ, hδr, Q, C, hQ, hQc, hQcenter, hcore, hCs,
      hcyl, hCrim, hCinside, hconstant, hmatched⟩ :=
    exists_terminal_upper_family_matched_normalizations_of_prepared data hg Φ χ H hH hχ
      hplanar hlabels E F hEheight hEcore hFband hFpoint hgerms
  choose l s hs hl A Na Nm hNac hNmc hbuffer hA hNa hNm using hmatched
  choose η hη hhalf using hbuffer
  let idx : data.ends.UpperCutIndex → Fin 3 := fun j => data.labels.symm (.inr j)
  have hidx : Injective idx := data.labels.symm.injective.comp Sum.inr_injective
  have hlabel (j : data.ends.UpperCutIndex) : data.labels (idx j) = .inr j :=
    data.labels.apply_symm_apply _
  let actual (j : data.ends.UpperCutIndex) : Set E3 :=
    (E ∘ g) '' terminalEndCap data.ends (.inr j)
  let model (j : data.ends.UpperCutIndex) : Set E3 :=
    (fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ''
      data.toTerminalSaddleGeometry.modelDomain (idx j)
  let band := data.toTerminalSaddleGeometry.flatten.symm '' data.toTerminalSaddleGeometry.modelBand
  let protectedSet := band ∪ {y | inner Real (M.v : E3) y ≤ c}
  have hv : ‖-(M.v : E3)‖ = 1 := by simpa only [norm_neg] using norm_eq_of_mem_sphere M.v
  have hQneg (y : E3) : inner Real (-(M.v : E3)) (Q y) = inner Real (-(M.v : E3)) y := by
    simp only [inner_neg_left, hQ]
  have hactualdis : Pairwise (fun i j => Disjoint (actual i) (actual j)) := by
    intro i j hij
    simpa only [actual, hlabel] using
      terminal_prepared_caps_disjoint data E (fun h => hij (hidx h))
        (i := idx i) (j := idx j)
  have hmodeldis : Pairwise (fun i j => Disjoint (model i) (model j)) := by
    intro i j hij
    exact terminal_physical_modelCaps_disjoint data (fun h => hij (hidx h))
  have hactualheight : ∀ j, ∀ y ∈ actual j,
      inner Real (-(M.v : E3)) y ≤ -data.ends.upperCut := by
    rintro j y ⟨q, hq, rfl⟩
    simp only [inner_neg_left, Function.comp_apply, hEheight, neg_le_neg_iff]
    exact terminal_upper_cap_height data j hq
  have hmodelheight : ∀ j, ∀ y ∈ model j,
      inner Real (-(M.v : E3)) y ≤ -data.ends.upperCut := by
    rintro j y ⟨q, hq, rfl⟩
    rw [inner_neg_left, neg_le_neg_iff]
    exact terminal_upper_model_domain_height data (idx j)
      (terminal_labeled_model_upper_boundary data Φ χ H hH hχ hplanar hlabels
        (idx j) j (hlabel j)).1 hq
  have hprotectedSet : IsClosed protectedSet :=
    (isClosed_terminal_physical_modelBand data).union (isClosed_le (by fun_prop) continuous_const)
  have hbandheight (y : E3) (hy : y ∈ band) :
      -data.ends.upperCut ≤ inner Real (-(M.v : E3)) y := by
    have hyflat : data.toTerminalSaddleGeometry.flatten y ∈ data.toTerminalSaddleGeometry.modelBand := by
      obtain ⟨x, hx, rfl⟩ := hy
      simpa only [Diffeomorph.apply_symm_apply] using hx
    have hh := ((terminal_physical_modelBand_mem_iff data y).mp hyflat).2.2
    rwa [inner_neg_left, neg_le_neg_iff]
  have hprotectedSetheight : ∀ y ∈ protectedSet, -data.ends.upperCut ≤ inner Real (-(M.v : E3)) y := by
    intro y hy
    rcases hy with hy | hy
    · exact hbandheight y hy
    · rw [inner_neg_left, neg_le_neg_iff]
      exact hy.trans hcu.le
  have hNaimage (j : data.ends.UpperCutIndex) : Na j '' actual j =
      liftPlaneDiffeomorph hv (l j) (s j) (hs j).ne (A j) ''
        boundedCylinderNorthernCap (-(M.v : E3)) ∪
      terminalCylinder (A j '' sphere (0 : Hemisphere.Plane (-(M.v : E3))) 1)
        (l j) (-data.ends.upperCut) := by
    simpa only [actual, data.labels.apply_symm_apply, ← hA j] using hNa j
  have hNmimage (j : data.ends.UpperCutIndex) : Nm j '' model j =
      liftPlaneDiffeomorph hv (l j) (s j) (hs j).ne (A j) ''
        boundedCylinderNorthernCap (-(M.v : E3)) ∪
      terminalCylinder (A j '' sphere (0 : Hemisphere.Plane (-(M.v : E3))) 1)
        (l j) (-data.ends.upperCut) := by
    simpa only [model, idx, ← hA j] using hNm j
  have havoid (i : data.ends.UpperCutIndex)
      (hposition : ∀ j, j ≠ i →
        Disjoint (A i '' closedBall 0 1) (A j '' closedBall 0 1) ∨
          A i '' closedBall 0 1 ⊆ A j '' ball 0 1) :
      ∃ R : Real, 0 < R ∧ ∀ y ∈ protectedSet,
        inner Real (-(M.v : E3)) y ≤ -data.ends.upperCut + 2 * R →
          (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto (Q y) ∉ A i '' ball 0 1 := by
    obtain ⟨R, hR, _, ha⟩ := exists_terminal_upper_band_avoidance
      data Φ χ H hH hχ hplanar hlabels hr Q hQ C hCs hcyl hCrim A
      (fun j => (hA j).symm) i hposition
    obtain ⟨w, hw, _, _, hwavoid⟩ := exists_band_and_halfspace_avoidance
      (neg_lt_neg hcu) Q (A i) hR ha
    refine ⟨w, hw, ?_⟩
    intro y hy hh
    apply hwavoid y _ hh
    simpa only [inner_neg_left, neg_le_neg_iff] using hy
  have hcard : Nat.card data.ends.UpperCutIndex = 1 ∨ Nat.card data.ends.UpperCutIndex = 2 :=
    (terminal_cap_label_counts data).elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
  obtain ⟨K, hK, R, hRoff, hRprotectedSet, hRimage⟩ :=
    exists_supported_small_cap_family_replacement_of_canonical_normalizations hcard hv
      (-data.ends.upperCut) A actual model hactualdis hmodeldis hactualheight hmodelheight
      l s hl hs Na Nm Q hQneg η hη
      (fun j y hy => (hhalf j y hy).1) (fun j y hy => (hhalf j y hy).2)
      hNac hNmc hNaimage hNmimage hprotectedSet hprotectedSetheight havoid
  refine ⟨K, hK, R, hRoff, hRprotectedSet, ?_⟩
  intro j
  rw [terminal_physical_modelCap_eq_image]
  exact hRimage j

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
