import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.PairedNormalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.UpperFamily

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

theorem exists_paired_terminal_upper_normalizations_with_common_preparation
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)
    (E F Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hEheight : ∀ y, inner Real (M.v : E3) (E y) = inner Real (M.v : E3) y)
    (hQheight : ∀ y, inner Real (M.v : E3) (Q y) = inner Real (M.v : E3) y)
    (hQcompact : ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Q y = y)
    (hQcentral : EqOn Q id {y | inner Real (M.v : E3) y = data.ends.upperCut})
    (hcore : ∀ D ∈ data.ends.caps,
      EqOn (Q ∘ E ∘ g) g (D.chart '' closedBall (0 : E2) 1))
    (hFband : EqOn F id data.toTerminalSaddleGeometry.modelBand)
    (hFpoint : ∀ q : S2, F (H (data.toTerminalSaddleGeometry.flatten (g q))) =
      data.toTerminalSaddleGeometry.flatten (E (g q)))
    (i : Fin 3) (j : data.ends.UpperCutIndex) (hlabel : data.labels i = Sum.inr j)
    {w : Real} (hw : 0 < w)
    (hconstant : ∀ z ∈ Icc data.ends.upperCut (data.ends.upperCut + w),
      range (fun q : S1 => (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
        (Q (E (g ((data.ends.upper j.1.1 j.1.2 j.2).chart (q, z)))))) =
      range (fun q : S1 => (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
        (E (g (data.ends.upperCutCircle j q)))))
    {r : Real} (hr : 0 < r) (C : OpenPartialHomeomorph (S1 × Real) S2)
    (hCs : C.source = univ ×ˢ Ioo (-r) r)
    (hCcylinder : ∀ q z, z ∈ Ioo (-r) r →
      Q (data.toTerminalSaddleGeometry.filledModel (C (q, z))) =
        (-data.ends.upperCut + z) • (-(M.v : E3)) +
          ((Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
            (data.toTerminalSaddleGeometry.filledModel (C (q, 0))) : E3))
    (hCrim : range (fun q : S1 => C (q, 0)) = data.modelDisk i '' sphere (0 : E2) 1)
    (hCinside : ∀ q z, z ∈ Ioo (-r) 0 → C (q, z) ∈ data.modelDisk i '' ball (0 : E2) 1) :
    let γ : S1 → Hemisphere.Plane (-(M.v : E3)) := fun q =>
      (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
        (data.toTerminalSaddleGeometry.filledModel (C (q, 0)))
    ∃ la lm sa sm : Real, ∃ hsa : sa < 0, ∃ hsm : sm < 0,
      la < -data.ends.upperCut ∧ lm < -data.ends.upperCut ∧
      ∃ A B : (Hemisphere.Plane (-(M.v : E3))) ≃ₘ[Real] (Hemisphere.Plane (-(M.v : E3))),
      ∃ Na Nm : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Na y = y) ∧
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Nm y = y) ∧
        (∃ η : Real, 0 < η ∧ ∀ y, -data.ends.upperCut - η ≤ inner Real (-(M.v : E3)) y →
          Na y = Q y ∧ Nm y = Q y) ∧
        A '' sphere (0 : Hemisphere.Plane (-(M.v : E3))) 1 = range γ ∧
        B '' sphere (0 : Hemisphere.Plane (-(M.v : E3))) 1 = range γ ∧
        Na '' ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) =
          liftPlaneDiffeomorph (by simpa using norm_eq_of_mem_sphere M.v : ‖-(M.v : E3)‖ = 1) la sa hsa.ne A ''
            boundedCylinderNorthernCap (-(M.v : E3)) ∪ terminalCylinder (range γ) la (-data.ends.upperCut) ∧
        Nm '' ((fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ''
          data.toTerminalSaddleGeometry.modelDomain i) =
          liftPlaneDiffeomorph (by simpa using norm_eq_of_mem_sphere M.v : ‖-(M.v : E3)‖ = 1) lm sm hsm.ne B ''
            boundedCylinderNorthernCap (-(M.v : E3)) ∪ terminalCylinder (range γ) lm (-data.ends.upperCut) := by
  let γ : S1 → Hemisphere.Plane (-(M.v : E3)) := fun q =>
    (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
      (data.toTerminalSaddleGeometry.filledModel (C (q, 0)))
  have hQrim (q : S1) : Q (E (g (terminalActualCutCircle data i q))) =
      E (g (terminalActualCutCircle data i q)) := by
    apply hQcentral
    change inner Real (M.v : E3) (E (g (terminalActualCutCircle data i q))) = _
    rw [hEheight]
    simpa only [terminalActualCutCircle, hlabel, AnnularEndFamily.upperCutCircle] using
      (data.ends.upper j.1.1 j.1.2 j.2).actual_height q data.ends.upperCut ⟨le_rfl, j.2.le⟩
  have hrim : range (fun q : S1 => Q (E (g (terminalActualCutCircle data i q)))) =
      range (fun q : S1 => data.toTerminalSaddleGeometry.filledModel (C (q, 0))) := by
    simp only [hQrim]
    rw [prepared_terminal_labeled_physical_cutCircle_range data Φ χ H hH hχ hplanar hlabels
      E F hFband hFpoint i]
    change range ((fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ∘
      (fun q : S1 => data.modelDisk i q)) =
      range ((fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ∘
        (fun q : S1 => C (q, 0)))
    rw [range_comp, range_comp, hCrim]
    congr 1
    ext q
    exact ⟨fun ⟨x, hx⟩ => ⟨x, x.property, hx⟩,
      fun ⟨x, hx, heq⟩ => ⟨⟨x, hx⟩, heq⟩⟩
  have hproj : range (fun q : S1 => (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
      (Q (E (g (terminalActualCutCircle data i q))))) = range γ := by
    simpa only [← range_comp, Function.comp_def] using
      congrArg (fun S : Set E3 => (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto '' S) hrim
  have hQcut (q : S1) : Q (E (g (data.ends.upperCutCircle j q))) =
      E (g (data.ends.upperCutCircle j q)) := by
    simpa only [terminalActualCutCircle, hlabel] using hQrim q
  have hcpos : ∀ z ∈ Icc data.ends.upperCut (data.ends.upperCut + w),
      range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
        (Q (E (g ((data.ends.upper j.1.1 j.1.2 j.2).chart (q, z)))))) =
      range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
        (Q (E (g (terminalActualCutCircle data i q))))) := by
    intro z hz
    have hh := congrArg (fun S : Set (Hemisphere.Plane (-(M.v : E3))) =>
      (axisNegPlaneEquiv (M.v : E3)).symm '' S) (hconstant z hz)
    simpa only [← range_comp, Function.comp_def, ← axisNegPlaneEquiv_projection,
      LinearIsometryEquiv.symm_apply_apply, hQcut, terminalActualCutCircle, hlabel] using hh
  obtain ⟨v, b, c, la, sa, hsa0, horient, τa, hτa, A, Na, hNa, hNahalf, hA, hNaimage⟩ :=
    exists_terminal_actual_normalization_with_common_preparation data hg i E Q hEheight
      hQheight hQcompact hcore hw (by rw [hlabel]; exact hcpos)
  rcases horient with ⟨_, _, _, _, _, k, hk⟩ | ⟨rfl, rfl, rfl, hla, hsa, _⟩
  · rw [hlabel] at hk
    cases hk
  · have hv : ‖-(M.v : E3)‖ = 1 := by simpa using norm_eq_of_mem_sphere M.v
    have hQneg (y : E3) : inner Real (-(M.v : E3)) (Q y) = inner Real (-(M.v : E3)) y := by
      simp only [inner_neg_left, hQheight]
    obtain ⟨lm, sm, hsm, hlm, B, Nm, hNm, ⟨τm, hτm, hNmhalf⟩, hB, hNmimage⟩ :=
      exists_buffered_terminal_model_normalization_with_common_preparation data i hv
        (Or.inr ⟨rfl, rfl⟩)
        (by intro x hx; rw [inner_neg_left,
            (terminal_labeled_model_upper_boundary data Φ χ H hH hχ hplanar hlabels i j hlabel).2 x hx])
        Q hQneg hQcompact hr C hCs γ hCcylinder hCrim hCinside
    have hAneg : axisNegPlaneDiffeomorph (M.v : E3) A ''
        sphere (0 : Hemisphere.Plane (-(M.v : E3))) 1 = range γ := by
      rw [axisNegPlaneDiffeomorph_image_sphere, hA]
      simpa only [← range_comp, Function.comp_def, axisNegPlaneEquiv_projection] using hproj
    have hNaimageNeg : Na '' ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) =
        liftPlaneDiffeomorph hv (-la) (-sa) (neg_ne_zero.mpr hsa0)
          (axisNegPlaneDiffeomorph (M.v : E3) A) '' boundedCylinderNorthernCap (-(M.v : E3)) ∪
        terminalCylinder (range γ) (-la) (-data.ends.upperCut) := by
      rw [uIcc_of_ge hla.le] at hNaimage
      rw [← terminalCylinder_eq_height_product] at hNaimage
      rw [hNaimage]
      have heq := complete_canonical_cap_axis_neg (norm_eq_of_mem_sphere M.v) A
        (range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
          (Q (E (g (terminalActualCutCircle data i q))))))
        data.ends.upperCut la sa hsa0
      have hprojNeg : axisNegPlaneEquiv (M.v : E3) ''
          range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
            (Q (E (g (terminalActualCutCircle data i q))))) = range γ := by
        simpa only [← range_comp, Function.comp_def, axisNegPlaneEquiv_projection] using hproj
      rw [hprojNeg] at heq
      exact heq.symm
    refine ⟨-la, lm, -sa, sm, neg_neg_of_pos hsa, hsm, neg_lt_neg hla, hlm,
      axisNegPlaneDiffeomorph (M.v : E3) A, B, Na, Nm, hNa, hNm,
      ⟨min τa τm, lt_min hτa hτm, ?_⟩, hAneg, hB, hNaimageNeg, hNmimage⟩
    intro y hy
    exact ⟨hNahalf y (by linarith [min_le_left τa τm]),
      hNmhalf y (by linarith [min_le_right τa τm])⟩

theorem exists_matched_terminal_upper_normalizations_with_common_preparation
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)
    (E F Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hEheight : ∀ y, inner Real (M.v : E3) (E y) = inner Real (M.v : E3) y)
    (hQheight : ∀ y, inner Real (M.v : E3) (Q y) = inner Real (M.v : E3) y)
    (hQcompact : ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Q y = y)
    (hQcentral : EqOn Q id {y | inner Real (M.v : E3) y = data.ends.upperCut})
    (hcore : ∀ D ∈ data.ends.caps,
      EqOn (Q ∘ E ∘ g) g (D.chart '' closedBall (0 : E2) 1))
    (hFband : EqOn F id data.toTerminalSaddleGeometry.modelBand)
    (hFpoint : ∀ q : S2, F (H (data.toTerminalSaddleGeometry.flatten (g q))) =
      data.toTerminalSaddleGeometry.flatten (E (g q)))
    (i : Fin 3) (j : data.ends.UpperCutIndex) (hlabel : data.labels i = Sum.inr j)
    {w : Real} (hw : 0 < w)
    (hconstant : ∀ z ∈ Icc data.ends.upperCut (data.ends.upperCut + w),
      range (fun q : S1 => (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
        (Q (E (g ((data.ends.upper j.1.1 j.1.2 j.2).chart (q, z)))))) =
      range (fun q : S1 => (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
        (E (g (data.ends.upperCutCircle j q)))))
    {r : Real} (hr : 0 < r) (C : OpenPartialHomeomorph (S1 × Real) S2)
    (hCs : C.source = univ ×ˢ Ioo (-r) r)
    (hCcylinder : ∀ q z, z ∈ Ioo (-r) r →
      Q (data.toTerminalSaddleGeometry.filledModel (C (q, z))) =
        (-data.ends.upperCut + z) • (-(M.v : E3)) +
          ((Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
            (data.toTerminalSaddleGeometry.filledModel (C (q, 0))) : E3))
    (hCrim : range (fun q : S1 => C (q, 0)) = data.modelDisk i '' sphere (0 : E2) 1)
    (hCinside : ∀ q z, z ∈ Ioo (-r) 0 → C (q, z) ∈ data.modelDisk i '' ball (0 : E2) 1) :
    let γ : S1 → Hemisphere.Plane (-(M.v : E3)) := fun q =>
      (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
        (data.toTerminalSaddleGeometry.filledModel (C (q, 0)))
    ∃ l s : Real, ∃ hs : s < 0, l < (-data.ends.upperCut) ∧
      ∃ A : (Hemisphere.Plane (-(M.v : E3))) ≃ₘ[Real] (Hemisphere.Plane (-(M.v : E3))),
      ∃ Na Nm : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Na y = y) ∧
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Nm y = y) ∧
        (∃ η : Real, 0 < η ∧ ∀ y, (-data.ends.upperCut) - η ≤ inner Real (-(M.v : E3)) y →
          Na y = Q y ∧ Nm y = Q y) ∧
        A '' sphere (0 : Hemisphere.Plane (-(M.v : E3))) 1 = range γ ∧
        Na '' ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) =
          liftPlaneDiffeomorph (by simpa using norm_eq_of_mem_sphere M.v : ‖-(M.v : E3)‖ = 1) l s hs.ne A ''
            boundedCylinderNorthernCap (-(M.v : E3)) ∪ terminalCylinder (range γ) l (-data.ends.upperCut) ∧
        Nm '' ((fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ''
          data.toTerminalSaddleGeometry.modelDomain i) =
          liftPlaneDiffeomorph (by simpa using norm_eq_of_mem_sphere M.v : ‖-(M.v : E3)‖ = 1) l s hs.ne A ''
            boundedCylinderNorthernCap (-(M.v : E3)) ∪ terminalCylinder (range γ) l (-data.ends.upperCut) := by
  obtain ⟨la, lm, sa, sm, hsa, hsm, hla, hlm, A, B, Na, Nm, hNa, hNm,
      ⟨η, hη, hhalf⟩, hA, hB, hNaimage, hNmimage⟩ :=
    exists_paired_terminal_upper_normalizations_with_common_preparation data hg Φ χ H hH
      hχ hplanar hlabels E F Q hEheight hQheight hQcompact hQcentral hcore hFband
      hFpoint i j hlabel hw hconstant hr C hCs hCcylinder hCrim hCinside
  obtain ⟨c, hcb, K, hK, R, hRfix, hRhalf, hRimage⟩ :=
    exists_supported_complete_lower_cap_alignment_of_same_filling_boundary
      (by simpa using norm_eq_of_mem_sphere M.v : ‖-(M.v : E3)‖ = 1) B A (hB.trans hA.symm) hlm hla hsm hsa
  have hQneg (y : E3) : inner Real (-(M.v : E3)) (Q y) = inner Real (-(M.v : E3)) y := by
    simp only [inner_neg_left, hQheight]
  obtain ⟨Km, hKm, hNmfix⟩ := hNm
  let w := min η (((-data.ends.upperCut) - c) / 2)
  have hw : 0 < w := lt_min hη (by linarith)
  have hwη : w ≤ η := min_le_left _ _
  have hwc : w ≤ ((-data.ends.upperCut) - c) / 2 := min_le_right _ _
  refine ⟨la, sa, hsa, hla, A, Na, Nm.trans R, hNa,
    ⟨Km ∪ K, hKm.union hK, ?_⟩, ⟨w, hw, ?_⟩, hA, hNaimage, ?_⟩
  · intro y hy
    change R (Nm y) = y
    rw [hNmfix y (fun h => hy (Or.inl h)), hRfix y (fun h => hy (Or.inr h))]
  · intro y hy
    have hyη : (-data.ends.upperCut) - η ≤ inner Real (-(M.v : E3)) y := by linarith
    refine ⟨(hhalf y hyη).1, ?_⟩
    change R (Nm y) = Q y
    rw [(hhalf y hyη).2, hRhalf _ (by rw [hQneg]; linarith)]
  · change (R ∘ Nm) '' _ = _
    rw [image_comp, hNmimage]
    simpa only [hB] using hRimage

theorem exists_terminal_upper_family_matched_normalizations_of_prepared
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
        (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) ∩ U) :
    ∃ r δ : Real, 0 < r ∧ 0 < δ ∧ δ < r ∧
    ∃ Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
    ∃ C : data.ends.UpperCutIndex → OpenPartialHomeomorph (S1 × Real) S2,
      (∀ y, inner Real (M.v : E3) (Q y) = inner Real (M.v : E3) y) ∧
      (∃ S : Set E3, IsCompact S ∧ ∀ y ∉ S, Q y = y) ∧
      EqOn Q id {y | inner Real (M.v : E3) y = data.ends.upperCut} ∧
      (∀ D ∈ data.ends.caps, EqOn (Q ∘ E ∘ g) g (D.chart '' closedBall (0 : E2) 1)) ∧
      (∀ j, (C j).source = univ ×ˢ Ioo (-r) r) ∧
      (∀ j q z, z ∈ Ioo (-r) r →
        Q (data.toTerminalSaddleGeometry.filledModel (C j (q, z))) =
          (-data.ends.upperCut + z) • (-(M.v : E3)) +
            ((Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
              (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3)) ∧
      (∀ j, range (fun q : S1 => C j (q, 0)) =
        data.modelDisk (data.labels.symm (.inr j)) '' sphere (0 : E2) 1) ∧
      (∀ j q z, z ∈ Ioo (-r) 0 → C j (q, z) ∈
        data.modelDisk (data.labels.symm (.inr j)) '' ball (0 : E2) 1) ∧
      (∀ j z, z ∈ Icc (data.ends.upperCut - δ) (data.ends.upperCut + δ) →
        range (fun q : S1 => (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
          (Q (E (g ((data.ends.upper j.1.1 j.1.2 j.2).chart (q, z)))))) =
        range (fun q : S1 => (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
          (E (g (data.ends.upperCutCircle j q))))) ∧
      ∀ j : data.ends.UpperCutIndex,
        let γ : S1 → Hemisphere.Plane (-(M.v : E3)) := fun q =>
          (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
            (data.toTerminalSaddleGeometry.filledModel (C j (q, 0)))
        ∃ l s : Real, ∃ hs : s < 0, l < (-data.ends.upperCut) ∧
          ∃ A : (Hemisphere.Plane (-(M.v : E3))) ≃ₘ[Real] (Hemisphere.Plane (-(M.v : E3))),
          ∃ Na Nm : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
            (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Na y = y) ∧
            (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Nm y = y) ∧
            (∃ η : Real, 0 < η ∧ ∀ y, (-data.ends.upperCut) - η ≤ inner Real (-(M.v : E3)) y →
              Na y = Q y ∧ Nm y = Q y) ∧
            A '' sphere (0 : Hemisphere.Plane (-(M.v : E3))) 1 = range γ ∧
            Na '' ((E ∘ g) '' terminalEndCap data.ends (data.labels (data.labels.symm (.inr j)))) =
              liftPlaneDiffeomorph (by simpa using norm_eq_of_mem_sphere M.v : ‖-(M.v : E3)‖ = 1) l s hs.ne A ''
                boundedCylinderNorthernCap (-(M.v : E3)) ∪ terminalCylinder (range γ) l (-data.ends.upperCut) ∧
            Nm '' ((fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ''
              data.toTerminalSaddleGeometry.modelDomain (data.labels.symm (.inr j))) =
              liftPlaneDiffeomorph (by simpa using norm_eq_of_mem_sphere M.v : ‖-(M.v : E3)‖ = 1) l s hs.ne A ''
                boundedCylinderNorthernCap (-(M.v : E3)) ∪ terminalCylinder (range γ) l (-data.ends.upperCut) := by
  obtain ⟨r, δ, hr, hδ, hδr, Q, C, hQh, hQc, hQcenter, hcore, hCs,
      hCcyl, hCrim, hCinside, hconstant⟩ :=
    exists_terminal_upper_family_common_preparation_of_prepared data hg Φ χ H hH hχ
      hplanar hlabels E F hEheight hEcore hFband hFpoint hgerms
  refine ⟨r, δ, hr, hδ, hδr, Q, C, hQh, hQc, hQcenter, hcore, hCs,
    hCcyl, hCrim, hCinside, hconstant, ?_⟩
  intro j
  exact exists_matched_terminal_upper_normalizations_with_common_preparation
    data hg Φ χ H hH hχ hplanar hlabels E F Q hEheight hQh hQc hQcenter hcore hFband hFpoint
    (data.labels.symm (.inr j)) j (data.labels.apply_symm_apply _) hδ
    (fun z hz => hconstant j z ⟨by linarith [hz.1], hz.2⟩)
    hr (C j) (hCs j) (hCcyl j) (hCrim j) (hCinside j)

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
