import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.ActualNormalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.ModelNormalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Replacement.Lower
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.TerminalFamily

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SaddleLevel SphereSurgeryCoreCap Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

theorem exists_supported_complete_lower_cap_alignment_of_same_filling_boundary
    {v : E3} (hv : ‖v‖ = 1)
    (A B : (Hemisphere.Plane v) ≃ₘ[Real] (Hemisphere.Plane v))
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 =
      B '' sphere (0 : Hemisphere.Plane v) 1)
    {da db b sa sb : Real} (hda : da < b) (hdb : db < b)
    (hsa : sa < 0) (hsb : sb < 0) :
    ∃ c : Real, c < b ∧ ∃ K : Set E3, IsCompact K ∧
      ∃ R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, R y = y) ∧ (∀ y, c ≤ inner Real v y → R y = y) ∧
        R '' (liftPlaneDiffeomorph hv da sa hsa.ne A '' boundedCylinderNorthernCap v ∪
          terminalCylinder (A '' sphere (0 : Hemisphere.Plane v) 1) da b) =
          liftPlaneDiffeomorph hv db sb hsb.ne B '' boundedCylinderNorthernCap v ∪
            terminalCylinder (A '' sphere (0 : Hemisphere.Plane v) 1) db b := by
  let J : E2 ≃ₗᵢ[Real] Hemisphere.Plane v :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 (by intro hv0; simp [hv0] at hv)).repr.symm
  let D := J.toContinuousLinearEquiv.toDiffeomorph.trans A
  let γ : S1 → Hemisphere.Plane v := fun q => A (J q)
  have hc := contMDiff_coe_sphere (n := 1) (m := ∞) (E := E2)
  have hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ := by
    apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
      (D.contMDiff.comp hc) (D.injective.comp Subtype.val_injective)
    intro q
    change Injective (mfderiv (𝓡 1) 𝓘(Real, Hemisphere.Plane v)
      (D ∘ (fun q : S1 => (q : E2))) q)
    rw [mfderiv_comp q (D.contMDiff.mdifferentiable (by simp) _)
      (hc.mdifferentiable (by simp) q)]
    exact (D.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      (by convert! injective_mvfderiv_subtypeVal_sphere q)
  have hA : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ := by
    change A '' sphere (0 : Hemisphere.Plane v) 1 =
      range (A ∘ J ∘ (fun q : S1 => (q : E2)))
    rw [range_comp, range_comp, Subtype.range_coe_subtype, ofPred_mem_eq,
      J.image_sphere, map_zero]
  obtain ⟨c, _, hcb, K, hK, R, hR, hhalf, hi⟩ :=
    exists_supported_complete_lower_cap_alignment hv γ hγ A B hA
      (hboundary.symm.trans hA) hda hdb hsa hsb
  exact ⟨c, hcb, K, hK, R, hR, hhalf, by simpa only [← hA] using hi⟩

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_paired_terminal_lower_normalizations_with_common_preparation
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
    (hQcentral : EqOn Q id {y | inner Real (M.v : E3) y = data.ends.lowerCut})
    (hcore : ∀ D ∈ data.ends.caps,
      EqOn (Q ∘ E ∘ g) g (D.chart '' closedBall (0 : E2) 1))
    (hFband : EqOn F id data.toTerminalSaddleGeometry.modelBand)
    (hFpoint : ∀ q : S2, F (H (data.toTerminalSaddleGeometry.flatten (g q))) =
      data.toTerminalSaddleGeometry.flatten (E (g q)))
    (i : Fin 3) (j : data.ends.LowerCutIndex) (hlabel : data.labels i = Sum.inl j)
    {w : Real} (hw : 0 < w)
    (hconstant : ∀ z ∈ Icc (data.ends.lowerCut - w) data.ends.lowerCut,
      range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
        (Q (E (g ((data.ends.lower j.1.1 j.1.2 j.2).chart (q, z)))))) =
      range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
        (E (g (data.ends.lowerCutCircle j q)))))
    {r : Real} (hr : 0 < r) (C : OpenPartialHomeomorph (S1 × Real) S2)
    (hCs : C.source = univ ×ˢ Ioo (-r) r)
    (hCcylinder : ∀ q z, z ∈ Ioo (-r) r →
      Q (data.toTerminalSaddleGeometry.filledModel (C (q, z))) =
        (data.ends.lowerCut + z) • (M.v : E3) +
          ((Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
            (data.toTerminalSaddleGeometry.filledModel (C (q, 0))) : E3))
    (hCrim : range (fun q : S1 => C (q, 0)) = data.modelDisk i '' sphere (0 : E2) 1)
    (hCinside : ∀ q z, z ∈ Ioo (-r) 0 → C (q, z) ∈ data.modelDisk i '' ball (0 : E2) 1) :
    let γ : S1 → Hemisphere.Plane (M.v : E3) := fun q =>
      (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
        (data.toTerminalSaddleGeometry.filledModel (C (q, 0)))
    ∃ la lm sa sm : Real, ∃ hsa : sa < 0, ∃ hsm : sm < 0,
      la < data.ends.lowerCut ∧ lm < data.ends.lowerCut ∧
      ∃ A B : (Hemisphere.Plane (M.v : E3)) ≃ₘ[Real] (Hemisphere.Plane (M.v : E3)),
      ∃ Na Nm : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Na y = y) ∧
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Nm y = y) ∧
        (∃ η : Real, 0 < η ∧ ∀ y, data.ends.lowerCut - η ≤ inner Real (M.v : E3) y →
          Na y = Q y ∧ Nm y = Q y) ∧
        A '' sphere (0 : Hemisphere.Plane (M.v : E3)) 1 = range γ ∧
        B '' sphere (0 : Hemisphere.Plane (M.v : E3)) 1 = range γ ∧
        Na '' ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) =
          liftPlaneDiffeomorph (norm_eq_of_mem_sphere M.v) la sa hsa.ne A ''
            boundedCylinderNorthernCap (M.v : E3) ∪ terminalCylinder (range γ) la data.ends.lowerCut ∧
        Nm '' ((fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ''
          data.toTerminalSaddleGeometry.modelDomain i) =
          liftPlaneDiffeomorph (norm_eq_of_mem_sphere M.v) lm sm hsm.ne B ''
            boundedCylinderNorthernCap (M.v : E3) ∪ terminalCylinder (range γ) lm data.ends.lowerCut := by
  let γ : S1 → Hemisphere.Plane (M.v : E3) := fun q =>
    (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
      (data.toTerminalSaddleGeometry.filledModel (C (q, 0)))
  have hQrim (q : S1) : Q (E (g (terminalActualCutCircle data i q))) =
      E (g (terminalActualCutCircle data i q)) := by
    apply hQcentral
    change inner Real (M.v : E3) (E (g (terminalActualCutCircle data i q))) = _
    rw [hEheight]
    simpa only [terminalActualCutCircle, hlabel, AnnularEndFamily.lowerCutCircle] using
      (data.ends.lower j.1.1 j.1.2 j.2).actual_height q data.ends.lowerCut ⟨j.2.le, le_rfl⟩
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
  have hproj : range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
      (Q (E (g (terminalActualCutCircle data i q))))) = range γ := by
    simpa only [← range_comp, Function.comp_def] using
      congrArg (fun S : Set E3 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto '' S) hrim
  have hQcut (q : S1) : Q (E (g (data.ends.lowerCutCircle j q))) =
      E (g (data.ends.lowerCutCircle j q)) := by
    simpa only [terminalActualCutCircle, hlabel] using hQrim q
  obtain ⟨v, b, c, la, sa, hsa0, horient, τa, hτa, A, Na, hNa, hNahalf, hA, hNaimage⟩ :=
    exists_terminal_actual_normalization_with_common_preparation data hg i E Q hEheight
      hQheight hQcompact hcore hw (by
        rw [hlabel]
        simpa only [terminalActualCutCircle, hlabel, hQcut] using hconstant)
  rcases horient with ⟨rfl, rfl, rfl, hla, hsa, _⟩ | ⟨_, _, _, _, _, k, hk⟩
  · obtain ⟨lm, sm, hsm, hlm, B, Nm, hNm, ⟨τm, hτm, hNmhalf⟩, hB, hNmimage⟩ :=
      exists_buffered_terminal_model_normalization_with_common_preparation data i
        (norm_eq_of_mem_sphere M.v) (Or.inl ⟨rfl, rfl⟩)
        (terminal_labeled_model_lower_boundary data Φ χ H hH hχ hplanar hlabels i j hlabel).2
        Q hQheight hQcompact hr C hCs γ hCcylinder hCrim hCinside
    refine ⟨la, lm, sa, sm, hsa, hsm, hla, hlm, A, B, Na, Nm, hNa, hNm,
      ⟨min τa τm, lt_min hτa hτm, ?_⟩, hA.trans hproj, hB, ?_, hNmimage⟩
    · intro y hy
      exact ⟨hNahalf y (by linarith [min_le_left τa τm]),
        hNmhalf y (by linarith [min_le_right τa τm])⟩
    · rw [uIcc_of_le hla.le, hproj] at hNaimage
      rw [terminalCylinder_eq_height_product]
      exact hNaimage
  · rw [hlabel] at hk
    cases hk

theorem exists_matched_terminal_lower_normalizations_with_common_preparation
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
    (hQcentral : EqOn Q id {y | inner Real (M.v : E3) y = data.ends.lowerCut})
    (hcore : ∀ D ∈ data.ends.caps,
      EqOn (Q ∘ E ∘ g) g (D.chart '' closedBall (0 : E2) 1))
    (hFband : EqOn F id data.toTerminalSaddleGeometry.modelBand)
    (hFpoint : ∀ q : S2, F (H (data.toTerminalSaddleGeometry.flatten (g q))) =
      data.toTerminalSaddleGeometry.flatten (E (g q)))
    (i : Fin 3) (j : data.ends.LowerCutIndex) (hlabel : data.labels i = Sum.inl j)
    {w : Real} (hw : 0 < w)
    (hconstant : ∀ z ∈ Icc (data.ends.lowerCut - w) data.ends.lowerCut,
      range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
        (Q (E (g ((data.ends.lower j.1.1 j.1.2 j.2).chart (q, z)))))) =
      range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
        (E (g (data.ends.lowerCutCircle j q)))))
    {r : Real} (hr : 0 < r) (C : OpenPartialHomeomorph (S1 × Real) S2)
    (hCs : C.source = univ ×ˢ Ioo (-r) r)
    (hCcylinder : ∀ q z, z ∈ Ioo (-r) r →
      Q (data.toTerminalSaddleGeometry.filledModel (C (q, z))) =
        (data.ends.lowerCut + z) • (M.v : E3) +
          ((Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
            (data.toTerminalSaddleGeometry.filledModel (C (q, 0))) : E3))
    (hCrim : range (fun q : S1 => C (q, 0)) = data.modelDisk i '' sphere (0 : E2) 1)
    (hCinside : ∀ q z, z ∈ Ioo (-r) 0 → C (q, z) ∈ data.modelDisk i '' ball (0 : E2) 1) :
    let γ : S1 → Hemisphere.Plane (M.v : E3) := fun q =>
      (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
        (data.toTerminalSaddleGeometry.filledModel (C (q, 0)))
    ∃ l s : Real, ∃ hs : s < 0, l < data.ends.lowerCut ∧
      ∃ A : (Hemisphere.Plane (M.v : E3)) ≃ₘ[Real] (Hemisphere.Plane (M.v : E3)),
      ∃ Na Nm : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Na y = y) ∧
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Nm y = y) ∧
        (∃ η : Real, 0 < η ∧ ∀ y, data.ends.lowerCut - η ≤ inner Real (M.v : E3) y →
          Na y = Q y ∧ Nm y = Q y) ∧
        A '' sphere (0 : Hemisphere.Plane (M.v : E3)) 1 = range γ ∧
        Na '' ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) =
          liftPlaneDiffeomorph (norm_eq_of_mem_sphere M.v) l s hs.ne A ''
            boundedCylinderNorthernCap (M.v : E3) ∪ terminalCylinder (range γ) l data.ends.lowerCut ∧
        Nm '' ((fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ''
          data.toTerminalSaddleGeometry.modelDomain i) =
          liftPlaneDiffeomorph (norm_eq_of_mem_sphere M.v) l s hs.ne A ''
            boundedCylinderNorthernCap (M.v : E3) ∪ terminalCylinder (range γ) l data.ends.lowerCut := by
  obtain ⟨la, lm, sa, sm, hsa, hsm, hla, hlm, A, B, Na, Nm, hNa, hNm,
      ⟨η, hη, hhalf⟩, hA, hB, hNaimage, hNmimage⟩ :=
    exists_paired_terminal_lower_normalizations_with_common_preparation data hg Φ χ H hH
      hχ hplanar hlabels E F Q hEheight hQheight hQcompact hQcentral hcore hFband
      hFpoint i j hlabel hw hconstant hr C hCs hCcylinder hCrim hCinside
  obtain ⟨c, hcb, K, hK, R, hRfix, hRhalf, hRimage⟩ :=
    exists_supported_complete_lower_cap_alignment_of_same_filling_boundary
      (norm_eq_of_mem_sphere M.v) B A (hB.trans hA.symm) hlm hla hsm hsa
  obtain ⟨Km, hKm, hNmfix⟩ := hNm
  let w := min η ((data.ends.lowerCut - c) / 2)
  have hw : 0 < w := lt_min hη (by linarith)
  have hwη : w ≤ η := min_le_left _ _
  have hwc : w ≤ (data.ends.lowerCut - c) / 2 := min_le_right _ _
  refine ⟨la, sa, hsa, hla, A, Na, Nm.trans R, hNa,
    ⟨Km ∪ K, hKm.union hK, ?_⟩, ⟨w, hw, ?_⟩, hA, hNaimage, ?_⟩
  · intro y hy
    change R (Nm y) = y
    rw [hNmfix y (fun h => hy (Or.inl h)), hRfix y (fun h => hy (Or.inr h))]
  · intro y hy
    have hyη : data.ends.lowerCut - η ≤ inner Real (M.v : E3) y := by linarith
    refine ⟨(hhalf y hyη).1, ?_⟩
    change R (Nm y) = Q y
    rw [(hhalf y hyη).2, hRhalf _ (by rw [hQheight]; linarith)]
  · change (R ∘ Nm) '' _ = _
    rw [image_comp, hNmimage]
    simpa only [hB] using hRimage

theorem exists_terminal_lower_family_paired_normalizations
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hzero : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (χ : Real → Real) (hχsmooth : ContDiff Real ∞ χ)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand) :
    ∃ E : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, inner Real (M.v : E3) (E y) = inner Real (M.v : E3) y) ∧
      (∀ D ∈ data.ends.caps, EqOn (E ∘ g) g (D.chart '' closedBall (0 : E2) 1)) ∧
      ∃ K : Set E3, IsCompact K ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, F y = y) ∧ EqOn F id data.toTerminalSaddleGeometry.modelBand ∧
        (∀ q : S2, F (H (data.toTerminalSaddleGeometry.flatten (g q))) =
          data.toTerminalSaddleGeometry.flatten (E (g q))) ∧
        (∀ i, F '' (H '' data.toTerminalSaddleGeometry.C i) =
          (data.toTerminalSaddleGeometry.flatten ∘ E ∘ g) ''
            terminalEndCap data.ends (data.labels i)) ∧
        ∃ r δ : Real, 0 < r ∧ 0 < δ ∧ δ < r ∧
        ∃ Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        ∃ C : data.ends.LowerCutIndex → OpenPartialHomeomorph (S1 × Real) S2,
          (∀ y, inner Real (M.v : E3) (Q y) = inner Real (M.v : E3) y) ∧
          (∃ S : Set E3, IsCompact S ∧ ∀ y ∉ S, Q y = y) ∧
          EqOn Q id {y | inner Real (M.v : E3) y = data.ends.lowerCut} ∧
          (∀ D ∈ data.ends.caps, EqOn (Q ∘ E ∘ g) g (D.chart '' closedBall (0 : E2) 1)) ∧
          (∀ j, (C j).source = univ ×ˢ Ioo (-r) r) ∧
          (∀ j q z, z ∈ Ioo (-r) r →
            Q (data.toTerminalSaddleGeometry.filledModel (C j (q, z))) =
              (data.ends.lowerCut + z) • (M.v : E3) +
                ((Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
                  (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3)) ∧
          (∀ j, range (fun q : S1 => C j (q, 0)) =
            data.modelDisk (data.labels.symm (.inl j)) '' sphere (0 : E2) 1) ∧
          (∀ j q z, z ∈ Ioo (-r) 0 → C j (q, z) ∈
            data.modelDisk (data.labels.symm (.inl j)) '' ball (0 : E2) 1) ∧
          (∀ j z, z ∈ Icc (data.ends.lowerCut - δ) (data.ends.lowerCut + δ) →
            range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
              (Q (E (g ((data.ends.lower j.1.1 j.1.2 j.2).chart (q, z)))))) =
            range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
              (E (g (data.ends.lowerCutCircle j q))))) ∧
          ∀ j : data.ends.LowerCutIndex,
            let γ : S1 → Hemisphere.Plane (M.v : E3) := fun q =>
              (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
                (data.toTerminalSaddleGeometry.filledModel (C j (q, 0)))
            ∃ la lm sa sm : Real, ∃ hsa : sa < 0, ∃ hsm : sm < 0,
              la < data.ends.lowerCut ∧ lm < data.ends.lowerCut ∧
              ∃ A B : (Hemisphere.Plane (M.v : E3)) ≃ₘ[Real] (Hemisphere.Plane (M.v : E3)),
              ∃ Na Nm : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
                (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Na y = y) ∧
                (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Nm y = y) ∧
                (∃ η : Real, 0 < η ∧ ∀ y, data.ends.lowerCut - η ≤ inner Real (M.v : E3) y →
                  Na y = Q y ∧ Nm y = Q y) ∧
                A '' sphere (0 : Hemisphere.Plane (M.v : E3)) 1 = range γ ∧
                B '' sphere (0 : Hemisphere.Plane (M.v : E3)) 1 = range γ ∧
                Na '' ((E ∘ g) '' terminalEndCap data.ends (data.labels (data.labels.symm (.inl j)))) =
                  liftPlaneDiffeomorph (norm_eq_of_mem_sphere M.v) la sa hsa.ne A ''
                    boundedCylinderNorthernCap (M.v : E3) ∪ terminalCylinder (range γ) la data.ends.lowerCut ∧
                Nm '' ((fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ''
                  data.toTerminalSaddleGeometry.modelDomain (data.labels.symm (.inl j))) =
                  liftPlaneDiffeomorph (norm_eq_of_mem_sphere M.v) lm sm hsm.ne B ''
                    boundedCylinderNorthernCap (M.v : E3) ∪ terminalCylinder (range γ) lm data.ends.lowerCut := by
  obtain ⟨E, hEh, hEc, K, hK, F, hF, hFb, hFp, hFc, r, δ, hr, hδ, hδr,
      Q, C, hQh, hQc, hQcenter, hcore, hCs, hCcyl, hCrim, hCinside, hconstant⟩ :=
    exists_terminal_lower_family_common_preparation data hg Φ hzero hΦ hΦinv χ hχsmooth
      H hH hχ hplanar hlabels
  refine ⟨E, hEh, hEc, K, hK, F, hF, hFb, hFp, hFc, r, δ, hr, hδ, hδr,
    Q, C, hQh, hQc, hQcenter, hcore, hCs, hCcyl, hCrim, hCinside, hconstant, ?_⟩
  intro j
  exact exists_paired_terminal_lower_normalizations_with_common_preparation
    data hg Φ χ H hH hχ hplanar hlabels E F Q hEh hQh hQc hQcenter hcore hFb hFp
    (data.labels.symm (.inl j)) j (data.labels.apply_symm_apply _) hδ
    (fun z hz => hconstant j z ⟨hz.1, by linarith [hz.2]⟩)
    hr (C j) (hCs j) (hCcyl j) (hCrim j) (hCinside j)

theorem exists_terminal_lower_family_matched_normalizations
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hzero : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (χ : Real → Real) (hχsmooth : ContDiff Real ∞ χ)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand) :
    ∃ E : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, inner Real (M.v : E3) (E y) = inner Real (M.v : E3) y) ∧
      (∀ D ∈ data.ends.caps, EqOn (E ∘ g) g (D.chart '' closedBall (0 : E2) 1)) ∧
      ∃ K : Set E3, IsCompact K ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, F y = y) ∧ EqOn F id data.toTerminalSaddleGeometry.modelBand ∧
        (∀ q : S2, F (H (data.toTerminalSaddleGeometry.flatten (g q))) =
          data.toTerminalSaddleGeometry.flatten (E (g q))) ∧
        (∀ i, F '' (H '' data.toTerminalSaddleGeometry.C i) =
          (data.toTerminalSaddleGeometry.flatten ∘ E ∘ g) ''
            terminalEndCap data.ends (data.labels i)) ∧
        ∃ r δ : Real, 0 < r ∧ 0 < δ ∧ δ < r ∧
        ∃ Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        ∃ C : data.ends.LowerCutIndex → OpenPartialHomeomorph (S1 × Real) S2,
          (∀ y, inner Real (M.v : E3) (Q y) = inner Real (M.v : E3) y) ∧
          (∃ S : Set E3, IsCompact S ∧ ∀ y ∉ S, Q y = y) ∧
          EqOn Q id {y | inner Real (M.v : E3) y = data.ends.lowerCut} ∧
          (∀ D ∈ data.ends.caps, EqOn (Q ∘ E ∘ g) g (D.chart '' closedBall (0 : E2) 1)) ∧
          (∀ j, (C j).source = univ ×ˢ Ioo (-r) r) ∧
          (∀ j q z, z ∈ Ioo (-r) r →
            Q (data.toTerminalSaddleGeometry.filledModel (C j (q, z))) =
              (data.ends.lowerCut + z) • (M.v : E3) +
                ((Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
                  (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3)) ∧
          (∀ j, range (fun q : S1 => C j (q, 0)) =
            data.modelDisk (data.labels.symm (.inl j)) '' sphere (0 : E2) 1) ∧
          (∀ j q z, z ∈ Ioo (-r) 0 → C j (q, z) ∈
            data.modelDisk (data.labels.symm (.inl j)) '' ball (0 : E2) 1) ∧
          (∀ j z, z ∈ Icc (data.ends.lowerCut - δ) (data.ends.lowerCut + δ) →
            range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
              (Q (E (g ((data.ends.lower j.1.1 j.1.2 j.2).chart (q, z)))))) =
            range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
              (E (g (data.ends.lowerCutCircle j q))))) ∧
          ∀ j : data.ends.LowerCutIndex,
            let γ : S1 → Hemisphere.Plane (M.v : E3) := fun q =>
              (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
                (data.toTerminalSaddleGeometry.filledModel (C j (q, 0)))
            ∃ l s : Real, ∃ hs : s < 0, l < data.ends.lowerCut ∧
              ∃ A : (Hemisphere.Plane (M.v : E3)) ≃ₘ[Real] (Hemisphere.Plane (M.v : E3)),
              ∃ Na Nm : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
                (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Na y = y) ∧
                (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Nm y = y) ∧
                (∃ η : Real, 0 < η ∧ ∀ y, data.ends.lowerCut - η ≤ inner Real (M.v : E3) y →
                  Na y = Q y ∧ Nm y = Q y) ∧
                A '' sphere (0 : Hemisphere.Plane (M.v : E3)) 1 = range γ ∧
                Na '' ((E ∘ g) '' terminalEndCap data.ends (data.labels (data.labels.symm (.inl j)))) =
                  liftPlaneDiffeomorph (norm_eq_of_mem_sphere M.v) l s hs.ne A ''
                    boundedCylinderNorthernCap (M.v : E3) ∪ terminalCylinder (range γ) l data.ends.lowerCut ∧
                Nm '' ((fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ''
                  data.toTerminalSaddleGeometry.modelDomain (data.labels.symm (.inl j))) =
                  liftPlaneDiffeomorph (norm_eq_of_mem_sphere M.v) l s hs.ne A ''
                    boundedCylinderNorthernCap (M.v : E3) ∪ terminalCylinder (range γ) l data.ends.lowerCut := by
  obtain ⟨E, hEh, hEc, K, hK, F, hF, hFb, hFp, hFc, r, δ, hr, hδ, hδr,
      Q, C, hQh, hQc, hQcenter, hcore, hCs, hCcyl, hCrim, hCinside, hconstant⟩ :=
    exists_terminal_lower_family_common_preparation data hg Φ hzero hΦ hΦinv χ hχsmooth
      H hH hχ hplanar hlabels
  refine ⟨E, hEh, hEc, K, hK, F, hF, hFb, hFp, hFc, r, δ, hr, hδ, hδr,
    Q, C, hQh, hQc, hQcenter, hcore, hCs, hCcyl, hCrim, hCinside, hconstant, ?_⟩
  intro j
  exact exists_matched_terminal_lower_normalizations_with_common_preparation
    data hg Φ χ H hH hχ hplanar hlabels E F Q hEh hQh hQc hQcenter hcore hFb hFp
    (data.labels.symm (.inl j)) j (data.labels.apply_symm_apply _) hδ
    (fun z hz => hconstant j z ⟨hz.1, by linarith [hz.2]⟩)
    hr (C j) (hCs j) (hCcyl j) (hCrim j) (hCinside j)

theorem exists_terminal_lower_family_matched_normalizations_of_prepared
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
    ∃ C : data.ends.LowerCutIndex → OpenPartialHomeomorph (S1 × Real) S2,
      (∀ y, inner Real (M.v : E3) (Q y) = inner Real (M.v : E3) y) ∧
      (∃ S : Set E3, IsCompact S ∧ ∀ y ∉ S, Q y = y) ∧
      EqOn Q id {y | inner Real (M.v : E3) y = data.ends.lowerCut} ∧
      (∀ D ∈ data.ends.caps, EqOn (Q ∘ E ∘ g) g (D.chart '' closedBall (0 : E2) 1)) ∧
      (∀ j, (C j).source = univ ×ˢ Ioo (-r) r) ∧
      (∀ j q z, z ∈ Ioo (-r) r →
        Q (data.toTerminalSaddleGeometry.filledModel (C j (q, z))) =
          (data.ends.lowerCut + z) • (M.v : E3) +
            ((Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
              (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3)) ∧
      (∀ j, range (fun q : S1 => C j (q, 0)) =
        data.modelDisk (data.labels.symm (.inl j)) '' sphere (0 : E2) 1) ∧
      (∀ j q z, z ∈ Ioo (-r) 0 → C j (q, z) ∈
        data.modelDisk (data.labels.symm (.inl j)) '' ball (0 : E2) 1) ∧
      (∀ j z, z ∈ Icc (data.ends.lowerCut - δ) (data.ends.lowerCut + δ) →
        range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
          (Q (E (g ((data.ends.lower j.1.1 j.1.2 j.2).chart (q, z)))))) =
        range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
          (E (g (data.ends.lowerCutCircle j q))))) ∧
      ∀ j : data.ends.LowerCutIndex,
        let γ : S1 → Hemisphere.Plane (M.v : E3) := fun q =>
          (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
            (data.toTerminalSaddleGeometry.filledModel (C j (q, 0)))
        ∃ l s : Real, ∃ hs : s < 0, l < data.ends.lowerCut ∧
          ∃ A : (Hemisphere.Plane (M.v : E3)) ≃ₘ[Real] (Hemisphere.Plane (M.v : E3)),
          ∃ Na Nm : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
            (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Na y = y) ∧
            (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Nm y = y) ∧
            (∃ η : Real, 0 < η ∧ ∀ y, data.ends.lowerCut - η ≤ inner Real (M.v : E3) y →
              Na y = Q y ∧ Nm y = Q y) ∧
            A '' sphere (0 : Hemisphere.Plane (M.v : E3)) 1 = range γ ∧
            Na '' ((E ∘ g) '' terminalEndCap data.ends (data.labels (data.labels.symm (.inl j)))) =
              liftPlaneDiffeomorph (norm_eq_of_mem_sphere M.v) l s hs.ne A ''
                boundedCylinderNorthernCap (M.v : E3) ∪ terminalCylinder (range γ) l data.ends.lowerCut ∧
            Nm '' ((fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ''
              data.toTerminalSaddleGeometry.modelDomain (data.labels.symm (.inl j))) =
              liftPlaneDiffeomorph (norm_eq_of_mem_sphere M.v) l s hs.ne A ''
                boundedCylinderNorthernCap (M.v : E3) ∪ terminalCylinder (range γ) l data.ends.lowerCut := by
  obtain ⟨r, δ, hr, hδ, hδr, Q, C, hQh, hQc, hQcenter, hcore, hCs,
      hCcyl, hCrim, hCinside, hconstant⟩ :=
    exists_terminal_lower_family_common_preparation_of_prepared data hg Φ χ H hH hχ
      hplanar hlabels E F hEheight hEcore hFband hFpoint hgerms
  refine ⟨r, δ, hr, hδ, hδr, Q, C, hQh, hQc, hQcenter, hcore, hCs,
    hCcyl, hCrim, hCinside, hconstant, ?_⟩
  intro j
  exact exists_matched_terminal_lower_normalizations_with_common_preparation
    data hg Φ χ H hH hχ hplanar hlabels E F Q hEheight hQh hQc hQcenter hcore hFband hFpoint
    (data.labels.symm (.inl j)) j (data.labels.apply_symm_apply _) hδ
    (fun z hz => hconstant j z ⟨hz.1, by linarith [hz.2]⟩)
    hr (C j) (hCs j) (hCcyl j) (hCrim j) (hCinside j)

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
