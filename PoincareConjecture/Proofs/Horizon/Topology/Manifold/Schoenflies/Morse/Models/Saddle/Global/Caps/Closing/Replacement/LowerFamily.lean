import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.PairReplacement.SmallFamily
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.PairedNormalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.BandAvoidance
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.LabelCount
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Geometry.ProtectedRegion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Replacement.Geometry

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
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_terminal_lower_family_replacement_of_prepared
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
    {c : Real} (hlc : data.ends.lowerCut < c) (_hcu : c < data.ends.upperCut) :
    ∃ K : Set E3, IsCompact K ∧
      ∃ R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, R y = y) ∧
        EqOn R id (data.toTerminalSaddleGeometry.flatten.symm ''
          data.toTerminalSaddleGeometry.modelBand ∪ {y | c ≤ inner Real (M.v : E3) y}) ∧
        ∀ j : data.ends.LowerCutIndex,
          R '' ((E ∘ g) '' terminalEndCap data.ends (.inl j)) =
            data.toTerminalSaddleGeometry.flatten.symm ''
              data.toTerminalSaddleGeometry.modelCaps (data.labels.symm (.inl j)) := by
  classical
  obtain ⟨r, δ, hr, hδ, hδr, Q, C, hQ, hQc, hQcenter, hcore, hCs,
      hcyl, hCrim, hCinside, hconstant, hnormal⟩ :=
    exists_terminal_lower_family_matched_normalizations_of_prepared data hg Φ χ H hH hχ
      hplanar hlabels E F hEheight hEcore hFband hFpoint hgerms
  choose a s hs ha A Na Nm hNac hNmc hbuffer hA hNa hNm using hnormal
  choose η hη hhalf using hbuffer
  let idx : data.ends.LowerCutIndex → Fin 3 := fun j => data.labels.symm (.inl j)
  have hidx : Injective idx := data.labels.symm.injective.comp Sum.inl_injective
  let actual : data.ends.LowerCutIndex → Set E3 :=
    fun j => (E ∘ g) '' terminalEndCap data.ends (.inl j)
  let model : data.ends.LowerCutIndex → Set E3 :=
    fun j => (fun q : S2 => data.toTerminalSaddleGeometry.filledModel q) ''
      data.toTerminalSaddleGeometry.modelDomain (idx j)
  let band := data.toTerminalSaddleGeometry.flatten.symm '' data.toTerminalSaddleGeometry.modelBand
  have hbandclosed : IsClosed band :=
    ((isCompact_terminal_modelBand data).image
      data.toTerminalSaddleGeometry.flatten.symm.contMDiff.continuous).isClosed
  have hbandheight : ∀ y ∈ band, data.ends.lowerCut ≤ inner Real (M.v : E3) y := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    apply ((terminal_physical_modelBand_mem_iff data _).mp ?_).2.1
    simpa only [Diffeomorph.apply_symm_apply] using hz
  have hcard : Nat.card data.ends.LowerCutIndex = 1 ∨ Nat.card data.ends.LowerCutIndex = 2 :=
    (terminal_cap_label_counts data).imp And.left And.left
  obtain ⟨K, hK, R, hRoff, hRfix, hRcap⟩ :=
    exists_supported_small_cap_family_replacement_of_canonical_normalizations hcard
      (norm_eq_of_mem_sphere M.v) data.ends.lowerCut A actual model
      (by
        intro i j hij
        have hh := terminal_prepared_caps_disjoint data E (fun h => hij (hidx h))
        simpa only [idx, data.labels.apply_symm_apply] using hh)
      (fun _ _ hij => terminal_physical_modelCaps_disjoint data (fun h => hij (hidx h)))
      (by
        intro j y hy
        obtain ⟨q, hq, rfl⟩ := hy
        simpa only [comp_apply, hEheight] using terminal_lower_cap_height data j hq)
      (by
        intro j y hy
        obtain ⟨q, hq, rfl⟩ := hy
        exact terminal_lower_model_domain_height data (idx j)
          (terminal_labeled_model_lower_boundary data Φ χ H hH hχ hplanar hlabels
            (idx j) j (data.labels.apply_symm_apply _)).1 hq)
      a s ha hs Na Nm Q hQ η hη
      (fun j y hy => (hhalf j y hy).1) (fun j y hy => (hhalf j y hy).2)
      hNac hNmc
      (by
        intro j
        simpa only [data.labels.apply_symm_apply, ← hA j] using hNa j)
      (by intro j; simpa only [← hA j] using hNm j)
      (show IsClosed (band ∪ {y : E3 | c ≤ inner Real (M.v : E3) y}) from
        hbandclosed.union (isClosed_le continuous_const (by fun_prop)))
      (by
        intro y hy
        rcases hy with hy | hy
        · exact hbandheight y hy
        · exact hlc.le.trans hy)
      (by
        intro j hposition
        obtain ⟨w, hw, _, havoid⟩ := exists_terminal_lower_band_avoidance
          data Φ χ H hH hχ hplanar hlabels hr Q hQ C hCs hcyl hCrim
          A (fun k => (hA k).symm) j hposition
        obtain ⟨u, hu, _, _, hprotected⟩ := exists_band_and_halfspace_avoidance hlc Q (A j) hw havoid
        exact ⟨u, hu, hprotected⟩)
  refine ⟨K, hK, R, hRoff, hRfix, ?_⟩
  intro j
  rw [terminal_physical_modelCap_eq_image]
  exact hRcap j

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
