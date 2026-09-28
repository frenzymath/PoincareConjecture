import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Actual.TerminalNormalization
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CylindricalNormalizationUpper







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SphereSurgeryCoreCap SaddleLevel Poincare.Geometry.Euclidean _root_.Poincare.Geometry.Manifold

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

set_option maxHeartbeats 2000000 in




theorem exists_terminal_actual_normalization_with_common_preparation
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves) (i : Fin 3)
    (E Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hEheight : ∀ y, inner Real (M.v : E3) (E y) = inner Real (M.v : E3) y)
    (hQheight : ∀ y, inner Real (M.v : E3) (Q y) = inner Real (M.v : E3) y)
    (hQcompact : ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, Q y = y)
    (hcore : ∀ D ∈ data.ends.caps,
      EqOn (Q ∘ E ∘ g) g (D.chart '' closedBall (0 : E2) 1))
    {w : Real} (hw : 0 < w)
    (hconstant : match data.labels i with
      | .inl j => ∀ z ∈ Icc (data.ends.lowerCut - w) data.ends.lowerCut,
          range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
            (Q (E (g ((data.ends.lower j.1.1 j.1.2 j.2).chart (q, z)))))) =
          range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
            (Q (E (g (terminalActualCutCircle data i q)))))
      | .inr j => ∀ z ∈ Icc data.ends.upperCut (data.ends.upperCut + w),
          range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
            (Q (E (g ((data.ends.upper j.1.1 j.1.2 j.2).chart (q, z)))))) =
          range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
            (Q (E (g (terminalActualCutCircle data i q)))))) :
    ∃ v : E3, ∃ b c l s : Real, ∃ hs : s ≠ 0,
      ((v = (M.v : E3) ∧ b = data.ends.lowerCut ∧ c = data.ends.lowerCut ∧
          l < c ∧ s < 0 ∧ ∃ j, data.labels i = Sum.inl j) ∨
        (v = -(M.v : E3) ∧ b = -data.ends.upperCut ∧ c = data.ends.upperCut ∧
          c < l ∧ 0 < s ∧ ∃ j, data.labels i = Sum.inr j)) ∧
      ∃ τ : Real, 0 < τ ∧
      ∃ B : (Hemisphere.Plane (M.v : E3)) ≃ₘ[Real] (Hemisphere.Plane (M.v : E3)),
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, F y = y) ∧
        (∀ y, b - τ ≤ inner Real v y → F y = Q y) ∧
        B '' sphere (0 : Hemisphere.Plane (M.v : E3)) 1 =
          range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
            (Q (E (g (terminalActualCutCircle data i q))))) ∧
        F '' ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) =
          (liftPlaneDiffeomorph (norm_eq_of_mem_sphere M.v) l s hs B ''
            boundedCylinderNorthernCap (M.v : E3)) ∪
          (fun z : Real × Hemisphere.Plane (M.v : E3) => z.1 • (M.v : E3) + (z.2 : E3)) ''
            (uIcc l c ×ˢ range (fun q : S1 =>
              (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
                (Q (E (g (terminalActualCutCircle data i q)))))) := by
  let g' : S2 → E3 := Q ∘ E ∘ g
  let J := E.trans Q
  have hg0 := M.tree.embedding_of_mem_leaves hg
  have hg' : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g' := by
    apply isSmoothEmbedding_of_injective_mfderiv (J.contMDiff.comp hg0.contMDiff)
      (J.injective.comp hg0.isEmbedding.injective)
    intro q
    rw [mfderiv_comp q (J.contMDiff.mdifferentiable (by simp) _)
      (hg0.contMDiff.mdifferentiable (by simp) _)]
    exact (J.mfderivToContinuousLinearEquiv (by simp) (g q)).injective.comp
      (injective_mfderiv_sphere_embedding hg0 q)
  have hheight (q : S2) : inner Real (M.v : E3) (g' q) =
      inner Real (M.v : E3) (g q) := (hQheight _).trans (hEheight _)
  have hgerm : ∀ q ∈ P.core, data.ends.height =ᶠ[𝓝 q]
      (fun p => inner Real (M.v : E3) (g' p)) := by
    simpa only [hheight] using data.ends.height_germ
  have hsupport (R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
      (S : Set E3) (hS : IsCompact S) (hfix : ∀ y ∉ S, R y = y) :
      ∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, (Q.trans R) y = y := by
    obtain ⟨K, hK, hQfix⟩ := hQcompact
    refine ⟨K ∪ S, hK.union hS, ?_⟩
    intro y hy
    change R (Q y) = y
    rw [hQfix y (fun hh => hy (Or.inl hh)), hfix y (fun hh => hy (Or.inr hh))]
  generalize hlabel : data.labels i = j at hconstant ⊢
  rcases j with j | j
  · let A := (data.ends.lower j.1.1 j.1.2 j.2).congrEmbedding
      (hcore j.1.1 j.1.2) hheight
    have hrim (q : S1) : terminalActualCutCircle data i q = A.chart (q, data.ends.lowerCut) := by
      simp only [terminalActualCutCircle, hlabel]
      rfl
    have hc : ∀ z ∈ Icc (data.ends.lowerCut - w) data.ends.lowerCut,
        range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
          (g' (A.chart (q, z)))) =
        range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
          (g' (A.chart (q, data.ends.lowerCut)))) := by
      have hchart : A.chart = (data.ends.lower j.1.1 j.1.2 j.2).chart := rfl
      simpa only [hrim, g', Function.comp_apply, hchart] using hconstant
    obtain ⟨l, u, hl, hu, huw, hsep, B, S, hS, R, hB, hfix, hhalf, himage⟩ :=
      exists_supported_cylindrical_lower_terminal_end_normalization A hg'
        (data.ends.cap_center_bounds j.1.1 j.1.2).1.le j.2 hgerm hw hc
    have hcap : terminalEndCap data.ends (.inl j) = A.cappedRegion data.ends.lowerCut := by
      change A.region ∪ _ = _
      exact union_comm _ _
    refine ⟨M.v, data.ends.lowerCut, data.ends.lowerCut, l, j.1.1.scale, j.1.1.scale_ne_zero,
      Or.inl ⟨rfl, rfl, rfl, hl.trans j.2, A.scale_neg, j, rfl⟩,
      u / 4, by positivity, j.1.1.planeMap.trans B.symm, Q.trans R,
      hsupport R S hS hfix, ?_, ?_, ?_⟩
    · intro y hy
      exact hhalf (Q y) (by rw [hQheight]; exact hy)
    · simpa only [hrim, g', Function.comp_apply, congrEmbedding] using hB
    · rw [hcap, uIcc_of_le (hl.le.trans j.2.le)]
      simpa only [Diffeomorph.coe_trans, g', image_image, hrim,
        Function.comp_apply, congrEmbedding] using himage
  · let A := (data.ends.upper j.1.1 j.1.2 j.2).congrEmbedding
      (hcore j.1.1 j.1.2) hheight
    have hrim (q : S1) : terminalActualCutCircle data i q = A.chart (q, data.ends.upperCut) := by
      simp only [terminalActualCutCircle, hlabel]
      rfl
    have hc : ∀ z ∈ Icc data.ends.upperCut (data.ends.upperCut + w),
        range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
          (g' (A.chart (q, z)))) =
        range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
          (g' (A.chart (q, data.ends.upperCut)))) := by
      have hchart : A.chart = (data.ends.upper j.1.1 j.1.2 j.2).chart := rfl
      simpa only [hrim, g', Function.comp_apply, hchart] using hconstant
    obtain ⟨l, u, hl, hu, huw, hsep, B, S, hS, R, hB, hfix, hhalf, himage⟩ :=
      exists_supported_cylindrical_upper_terminal_end_normalization A hg'
        (data.ends.cap_center_bounds j.1.1 j.1.2).2.le j.2 hgerm hw hc
    have hcap : terminalEndCap data.ends (.inr j) = A.cappedRegion data.ends.upperCut := by
      change A.region ∪ _ = _
      rw [A.region_eq_image, UpperAnnularEnd.cappedRegion, union_comm]
      rfl
    refine ⟨-(M.v : E3), -data.ends.upperCut, data.ends.upperCut, l,
      j.1.1.scale, j.1.1.scale_ne_zero,
      Or.inr ⟨rfl, rfl, rfl, j.2.trans hl, A.scale_pos, j, rfl⟩,
      u / 4, by positivity, j.1.1.planeMap.trans B.symm, Q.trans R,
      hsupport R S hS hfix, ?_, ?_, ?_⟩
    · intro y hy
      change R (Q y) = Q y
      apply hhalf
      rw [hQheight]
      rw [inner_neg_left] at hy
      linarith
    · simpa only [hrim, g', Function.comp_apply, congrEmbedding] using hB
    · rw [hcap, uIcc_of_ge (j.2.le.trans hl.le)]
      simpa only [Diffeomorph.coe_trans, g', image_image, hrim,
        Function.comp_apply, congrEmbedding] using himage

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
