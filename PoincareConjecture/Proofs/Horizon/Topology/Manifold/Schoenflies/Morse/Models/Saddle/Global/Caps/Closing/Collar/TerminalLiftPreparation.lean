import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.SlabLiftPreparation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Family.ActualAnnuli
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Terminal



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SaddleLevel Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}




theorem exists_terminal_lift_preserving_inserted_caps
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hzero : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y) :
    let d := data.toTerminalSaddleGeometry
    ∃ τ : Real → Real, ContDiff Real ∞ τ ∧ EqOn τ χ d.I ∧
    ∃ L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, L y = d.flatten.symm
        (planarHeightMap Φ (τ (inner Real (M.v : E3) y)) (d.flatten y))) ∧
      (∀ y, inner Real (M.v : E3) (L y) = inner Real (M.v : E3) y) ∧
      (∀ D ∈ data.ends.caps, EqOn (L ∘ g) g (D.chart '' closedBall (0 : E2) 1)) ∧
      (∀ y, inner Real (M.v : E3) y ∈ d.I → L y = d.flatten.symm (H (d.flatten y))) ∧
      ∃ K : Set E3, IsCompact K ∧
        ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ y ∉ K, G y = y) ∧ EqOn G id {y | y 2 ∈ d.I} ∧
          (∀ q : S2, G (H (d.flatten (g q))) = d.flatten (L (g q))) ∧
          ∀ i, G '' (H '' d.C i) =
            (d.flatten ∘ L ∘ g) '' terminalEndCap data.ends (data.labels i) := by
  let d := data.toTerminalSaddleGeometry
  have hflat (y : E3) : d.flatten y 2 = inner Real (M.v : E3) y :=
    (data.frame_height (data.D y)).trans (data.D_height y)
  have hflati (y : E3) : inner Real (M.v : E3) (d.flatten.symm y) = y 2 := by
    rw [← hflat, d.flatten.apply_symm_apply]
  have hg' := M.tree.embedding_of_mem_leaves hg
  obtain ⟨a, δa, hδa, _, hgapA, hcentersA, _⟩ :=
    data.ends.exists_lower_common_physical_annuli hg' (norm_eq_of_mem_sphere M.v)
  obtain ⟨b, δb, hδb, _, hgapB, hcentersB, _⟩ :=
    data.ends.exists_upper_common_physical_annuli hg' (norm_eq_of_mem_sphere M.v)
  have hcompact : IsCompact (range (d.flatten ∘ g)) :=
    isCompact_range (d.flatten.continuous.comp hg'.contMDiff.continuous)
  obtain ⟨τ, hτ, hτχ, L₀, hL₀, hLheight, hLends, hLband, K, hK, G,
    hGfix, hGband, hpoint, _⟩ :=
    exists_supported_slab_lift_preparation Φ hzero hΦ hΦinv χ hχ H hH
      (show a < data.ends.lowerCut by linarith)
      (show data.ends.upperCut < b by linarith) hcompact
  let L := (d.flatten.trans L₀).trans d.flatten.symm
  have hL (y : E3) : L y = d.flatten.symm (L₀ (d.flatten y)) := rfl
  have hpoint' (q : S2) : G (H (d.flatten (g q))) = d.flatten (L (g q)) := by
    rw [hL, d.flatten.apply_symm_apply]
    exact hpoint _ ⟨q, rfl⟩
  refine ⟨τ, hτ, hτχ, L, ?_, ?_, ?_, ?_, K, hK, G, hGfix, hGband, hpoint', ?_⟩
  · intro y
    change L y = d.flatten.symm
      (toE3 (Φ (τ (inner Real (M.v : E3) y)) (d.flatten y 2)
        (toE2 (d.flatten y))) (d.flatten y 2))
    rw [hL, hL₀, hflat]
  · intro y
    rw [hL, hflati, hLheight, hflat]
  · intro D hD q hq
    have hdeep : d.flatten (g q) 2 ≤ a ∨ b ≤ d.flatten (g q) 2 := by
      rw [hflat]
      rcases data.ends.cap_side D hD with hlow | hupp
      · left
        have hc := hcentersA ⟨⟨D, hD⟩, hlow⟩
        have hh := (data.ends.lower D hD hlow).height_le_center_of_mem_cap hq
        dsimp only at hc
        linarith
      · right
        have hc := hcentersB ⟨⟨D, hD⟩, hupp⟩
        have hh := (data.ends.upper D hD hupp).reflected.height_le_center_of_mem_cap hq
        change inner Real (M.v : E3) (heightReflection D.unit_v (g q)) ≤ -D.center at hh
        rw [inner_heightReflection] at hh
        dsimp only at hc
        linarith
    change L (g q) = g q
    rw [hL, hLends _ hdeep, d.flatten.symm_apply_apply]
  · intro y hy
    rw [hL, hLband (by
      change d.flatten y 2 ∈ Icc data.ends.lowerCut data.ends.upperCut
      rw [hflat]
      exact hy)]
  · intro i
    change G '' (H '' ((d.flatten ∘ g) '' _)) = _
    rw [image_image, image_image]
    exact image_congr (fun q _ => hpoint' q)

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
