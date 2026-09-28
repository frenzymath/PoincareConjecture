import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CylindricalPreparationUpper

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SphereSurgeryCoreCap SaddleLevel Poincare.Geometry.Euclidean Poincare.Geometry.Manifold

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

def terminalActualCutCircle (data : TerminalSaddleData M P p e) (i : Fin 3) : S1 → S2 :=
  match data.labels i with
  | .inl j => data.ends.lowerCutCircle j
  | .inr j => data.ends.upperCutCircle j

theorem exists_terminal_actual_canonical_normalization_of_height_preserving_map
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves) (i : Fin 3)
    (E : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hEheight : ∀ y, inner Real (M.v : E3) (E y) = inner Real (M.v : E3) y)
    (hEcap : ∀ D ∈ data.ends.caps,
      EqOn (E ∘ g) g (D.chart '' closedBall (0 : E2) 1)) :
    ∃ v : E3, ∃ b c l s : Real, ∃ hs : s ≠ 0,
      ((v = (M.v : E3) ∧ b = data.ends.lowerCut ∧ c = data.ends.lowerCut ∧
          l < c ∧ s < 0 ∧ ∃ j, data.labels i = Sum.inl j) ∨
        (v = -(M.v : E3) ∧ b = -data.ends.upperCut ∧ c = data.ends.upperCut ∧
          c < l ∧ 0 < s ∧ ∃ j, data.labels i = Sum.inr j)) ∧
      ∃ τ : Real, 0 < τ ∧
      ∃ B : (Hemisphere.Plane (M.v : E3)) ≃ₘ[Real] (Hemisphere.Plane (M.v : E3)),
      ∃ G F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y, inner Real v (G y) = inner Real v y) ∧
        EqOn G id {y | inner Real v y = b} ∧
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, G y = y) ∧
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, F y = y) ∧
        (∀ y, b - τ ≤ inner Real v y → F y = G y) ∧
        B '' sphere (0 : Hemisphere.Plane (M.v : E3)) 1 =
          range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
            (E (g (terminalActualCutCircle data i q)))) ∧
        F '' ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) =
          (liftPlaneDiffeomorph (norm_eq_of_mem_sphere M.v) l s hs B ''
            boundedCylinderNorthernCap (M.v : E3)) ∪
          (fun z : Real × Hemisphere.Plane (M.v : E3) => z.1 • (M.v : E3) + (z.2 : E3)) ''
            (uIcc l c ×ˢ range (fun q : S1 =>
              (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
                (E (g (terminalActualCutCircle data i q))))) := by
  have hg0 := M.tree.embedding_of_mem_leaves hg
  have hge : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (E ∘ g) := by
    apply isSmoothEmbedding_of_injective_mfderiv (E.contMDiff.comp hg0.contMDiff)
      (E.injective.comp hg0.isEmbedding.injective)
    intro q
    rw [mfderiv_comp q (E.contMDiff.mdifferentiable (by simp) _)
      (hg0.contMDiff.mdifferentiable (by simp) _)]
    exact (E.mfderivToContinuousLinearEquiv (by simp) (g q)).injective.comp
      (injective_mfderiv_sphere_embedding hg0 q)
  have hheight (q : S2) : inner Real (M.v : E3) ((E ∘ g) q) =
      inner Real (M.v : E3) (g q) := hEheight (g q)
  have hgerm : ∀ q ∈ P.core, data.ends.height =ᶠ[𝓝 q]
      (fun p => inner Real (M.v : E3) ((E ∘ g) p)) := by
    simpa only [hheight] using data.ends.height_germ
  generalize hlabel : data.labels i = j
  rcases j with j | j
  · let A := (data.ends.lower j.1.1 j.1.2 j.2).congrEmbedding
      (hEcap j.1.1 j.1.2) hheight
    obtain ⟨r, l, u, hr, hrR, hl, hu, hur, hsep, G, F, Q,
      hGheight, hcentral, _, _, ⟨K, hK, _, hGfix⟩, hFsupport, hagree, hQ, hFimage⟩ :=
      exists_prepared_cylindrical_lower_terminal_end_normalization A hge
        (data.ends.cap_center_bounds j.1.1 j.1.2).1.le j.2 hgerm
    have hcap : terminalEndCap data.ends (.inl j) = A.cappedRegion data.ends.lowerCut := by
      change A.region ∪ _ = _
      exact union_comm _ _
    have hrim (q : S1) : terminalActualCutCircle data i q = A.chart (q, data.ends.lowerCut) := by
      simp only [terminalActualCutCircle, hlabel]
      rfl
    refine ⟨M.v, data.ends.lowerCut, data.ends.lowerCut, l, j.1.1.scale, j.1.1.scale_ne_zero,
      Or.inl ⟨rfl, rfl, rfl, hl.trans j.2, A.scale_neg, j, rfl⟩,
      u / 4, by positivity, j.1.1.planeMap.trans Q.symm, G, F, hGheight, hcentral,
      ⟨K, hK, hGfix⟩, hFsupport, hagree, ?_, ?_⟩
    · simpa only [hrim, Function.comp_apply, congrEmbedding] using hQ
    · rw [hcap, uIcc_of_le (hl.le.trans j.2.le)]
      simpa only [hrim, Function.comp_apply, congrEmbedding] using hFimage
  · let A := (data.ends.upper j.1.1 j.1.2 j.2).congrEmbedding
      (hEcap j.1.1 j.1.2) hheight
    obtain ⟨r, l, u, hr, hrR, hl, hu, hur, hsep, G, F, Q,
      hGheight, hcentral, _, _, ⟨K, hK, _, hGfix⟩, hFsupport, hagree, hQ, hFimage⟩ :=
      exists_prepared_cylindrical_upper_terminal_end_normalization A hge
        (data.ends.cap_center_bounds j.1.1 j.1.2).2.le j.2 hgerm
    have hcap : terminalEndCap data.ends (.inr j) = A.cappedRegion data.ends.upperCut := by
      change A.region ∪ _ = _
      rw [A.region_eq_image, UpperAnnularEnd.cappedRegion, union_comm]
      rfl
    have hrim (q : S1) : terminalActualCutCircle data i q = A.chart (q, data.ends.upperCut) := by
      simp only [terminalActualCutCircle, hlabel]
      rfl
    refine ⟨-(M.v : E3), -data.ends.upperCut, data.ends.upperCut, l,
      j.1.1.scale, j.1.1.scale_ne_zero,
      Or.inr ⟨rfl, rfl, rfl, j.2.trans hl, A.scale_pos, j, rfl⟩,
      u / 4, by positivity, j.1.1.planeMap.trans Q.symm, G, F, ?_, ?_,
      ⟨K, hK, hGfix⟩, hFsupport, ?_, ?_, ?_⟩
    · intro y
      simp only [inner_neg_left, hGheight]
    · intro y hy
      apply hcentral
      change inner Real (M.v : E3) y = data.ends.upperCut
      change inner Real (-(M.v : E3)) y = -data.ends.upperCut at hy
      simpa only [inner_neg_left, neg_inj] using hy
    · intro y hy
      apply hagree
      rw [inner_neg_left] at hy
      linarith
    · simpa only [hrim, Function.comp_apply, congrEmbedding] using hQ
    · rw [hcap, uIcc_of_ge (j.2.le.trans hl.le)]
      simpa only [hrim, Function.comp_apply, congrEmbedding] using hFimage

theorem exists_terminal_actual_canonical_normalization
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves) (i : Fin 3) :
    ∃ v : E3, ∃ b c l s : Real, ∃ hs : s ≠ 0,
      ((v = (M.v : E3) ∧ b = data.ends.lowerCut ∧ c = data.ends.lowerCut ∧
          l < c ∧ s < 0 ∧ ∃ j, data.labels i = Sum.inl j) ∨
        (v = -(M.v : E3) ∧ b = -data.ends.upperCut ∧ c = data.ends.upperCut ∧
          c < l ∧ 0 < s ∧ ∃ j, data.labels i = Sum.inr j)) ∧
      ∃ τ : Real, 0 < τ ∧
      ∃ B : (Hemisphere.Plane (M.v : E3)) ≃ₘ[Real] (Hemisphere.Plane (M.v : E3)),
      ∃ G F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y, inner Real v (G y) = inner Real v y) ∧
        EqOn G id {y | inner Real v y = b} ∧
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, G y = y) ∧
        (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, F y = y) ∧
        (∀ y, b - τ ≤ inner Real v y → F y = G y) ∧
        B '' sphere (0 : Hemisphere.Plane (M.v : E3)) 1 =
          range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
            (g (terminalActualCutCircle data i q))) ∧
        F '' (g '' terminalEndCap data.ends (data.labels i)) =
          (liftPlaneDiffeomorph (norm_eq_of_mem_sphere M.v) l s hs B ''
            boundedCylinderNorthernCap (M.v : E3)) ∪
          (fun z : Real × Hemisphere.Plane (M.v : E3) => z.1 • (M.v : E3) + (z.2 : E3)) ''
            (uIcc l c ×ˢ range (fun q : S1 =>
              (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
                (g (terminalActualCutCircle data i q)))) := by
  exact exists_terminal_actual_canonical_normalization_of_height_preserving_map
    data hg i (Diffeomorph.refl (𝓡 3) E3 ∞) (fun _ => rfl) (fun _ _ _ _ => rfl)

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
