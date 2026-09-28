import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.HorizontalComposition
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Replacement.Upper

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

def terminalCapProtectedHalfspace (data : TerminalSaddleData M P p e) (i : Fin 3) : Set E3 :=
  match data.labels i with
  | .inl _ => {y | data.ends.lowerCut ≤ inner Real (M.v : E3) y}
  | .inr _ => {y | inner Real (M.v : E3) y ≤ data.ends.upperCut}

def terminalCapBufferedProtectedHalfspace (data : TerminalSaddleData M P p e)
    (i : Fin 3) (η : Real) : Set E3 :=
  match data.labels i with
  | .inl _ => {y | data.ends.lowerCut - η ≤ inner Real (M.v : E3) y}
  | .inr _ => {y | inner Real (M.v : E3) y ≤ data.ends.upperCut + η}

theorem terminalCapProtectedHalfspace_subset_buffered
    (data : TerminalSaddleData M P p e) (i : Fin 3) {η : Real} (hη : 0 ≤ η) :
    terminalCapProtectedHalfspace data i ⊆ terminalCapBufferedProtectedHalfspace data i η := by
  cases hlabel : data.labels i <;>
    simp only [terminalCapProtectedHalfspace, terminalCapBufferedProtectedHalfspace, hlabel]
  · intro y hy
    change data.ends.lowerCut ≤ inner Real (M.v : E3) y at hy
    change data.ends.lowerCut - η ≤ inner Real (M.v : E3) y
    linarith
  · intro y hy
    change inner Real (M.v : E3) y ≤ data.ends.upperCut at hy
    change inner Real (M.v : E3) y ≤ data.ends.upperCut + η
    linarith

theorem physical_modelBand_subset_terminalCapProtectedHalfspace
    (data : TerminalSaddleData M P p e) (i : Fin 3) :
    data.toTerminalSaddleGeometry.flatten ⁻¹' data.toTerminalSaddleGeometry.modelBand ⊆
      terminalCapProtectedHalfspace data i := by
  intro y hy
  obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp hy
  have hheight : inner Real (M.v : E3) y ∈ data.toTerminalSaddleGeometry.I := by
    have hh : data.toTerminalSaddleGeometry.flatten y 2 ∈ data.toTerminalSaddleGeometry.I :=
      hyz.2.symm ▸ hz
    have hflat : data.toTerminalSaddleGeometry.flatten y 2 = inner Real (M.v : E3) y :=
      (data.frame_height (data.D y)).trans (data.D_height y)
    rwa [hflat] at hh
  generalize hlabel : data.labels i = j
  rcases j with j | j
  · simpa only [terminalCapProtectedHalfspace, hlabel, mem_ofPred_eq] using hheight.1
  · simpa only [terminalCapProtectedHalfspace, hlabel, mem_ofPred_eq] using hheight.2

theorem exists_flat_terminal_cap_replacement_of_prepared
    (data : TerminalSaddleData M P p e) (i : Fin 3)
    (H E F R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    {K L : Set E3} (hK : IsCompact K) (hL : IsCompact L)
    (hFfix : ∀ y ∉ K, F y = y)
    (hFband : EqOn F id data.toTerminalSaddleGeometry.modelBand)
    (hFcap : F '' (H '' data.toTerminalSaddleGeometry.C i) =
      (data.toTerminalSaddleGeometry.flatten ∘ E ∘ g) ''
        terminalEndCap data.ends (data.labels i))
    (hRfix : ∀ y ∉ L, R y = y)
    (hRhalf : EqOn R id (terminalCapProtectedHalfspace data i))
    (hRcap : R '' ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) =
      data.toTerminalSaddleGeometry.flatten.symm '' data.toTerminalSaddleGeometry.modelCaps i) :
    ∃ S : Set E3, IsCompact S ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ S, G y = y) ∧ EqOn G id data.toTerminalSaddleGeometry.modelBand ∧
        G '' (H '' data.toTerminalSaddleGeometry.C i) = data.toTerminalSaddleGeometry.modelCaps i := by
  let d := data.toTerminalSaddleGeometry
  let G := F.trans (d.flatten.symm.trans (R.trans d.flatten))
  have hG (y : E3) : G y = d.flatten (R (d.flatten.symm (F y))) := rfl
  refine ⟨K ∪ d.flatten '' L, hK.union (hL.image d.flatten.continuous), G, ?_, ?_, ?_⟩
  · intro y hy
    rw [hG, hFfix y (fun hh => hy (Or.inl hh))]
    have hnot : d.flatten.symm y ∉ L := fun hh =>
      hy (Or.inr ⟨d.flatten.symm y, hh, d.flatten.apply_symm_apply y⟩)
    rw [hRfix _ hnot, d.flatten.apply_symm_apply]
  · intro y hy
    rw [hG, hFband hy, id_eq]
    have hh : d.flatten.symm y ∈ terminalCapProtectedHalfspace data i :=
      physical_modelBand_subset_terminalCapProtectedHalfspace data i (by
        change d.flatten (d.flatten.symm y) ∈ d.modelBand
        rwa [d.flatten.apply_symm_apply])
    rw [hRhalf hh, id_eq, d.flatten.apply_symm_apply]
  · change (d.flatten ∘ R ∘ d.flatten.symm ∘ F) '' (H '' d.C i) = d.modelCaps i
    rw [image_comp, image_comp, image_comp, hFcap]
    have hcancel : d.flatten.symm '' ((d.flatten ∘ E ∘ g) ''
        terminalEndCap data.ends (data.labels i)) =
        (E ∘ g) '' terminalEndCap data.ends (data.labels i) := by
      rw [image_image]
      exact image_congr (fun q _ => d.flatten.symm_apply_apply (E (g q)))
    rw [hcancel, hRcap, image_image]
    change (fun y => d.flatten (d.flatten.symm y)) '' d.modelCaps i = d.modelCaps i
    simp only [Diffeomorph.apply_symm_apply, image_id']

theorem exists_buffered_prepared_terminal_cap_replacements
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
      (∀ i, ∃ U : Set E3, IsOpen U ∧
        (fun y => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ''
          sphere (0 : E2) 1 ⊆ U ∧
        ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) ∩ U =
          (data.toTerminalSaddleGeometry.flatten.symm ''
            data.toTerminalSaddleGeometry.modelCaps i) ∩ U ∧
        (E '' range g) ∩ U =
          (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) ∩ U) ∧
      ∃ K : Set E3, IsCompact K ∧
        ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ y ∉ K, F y = y) ∧ EqOn F id data.toTerminalSaddleGeometry.modelBand ∧
          (∀ q : S2, F (H (data.toTerminalSaddleGeometry.flatten (g q))) =
            data.toTerminalSaddleGeometry.flatten (E (g q))) ∧
          (∀ i, F '' (H '' data.toTerminalSaddleGeometry.C i) =
            (data.toTerminalSaddleGeometry.flatten ∘ E ∘ g) ''
              terminalEndCap data.ends (data.labels i)) ∧
          ∀ i, ∃ L : Set E3, IsCompact L ∧
            ∃ R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
              (∀ y ∉ L, R y = y) ∧ (∃ η : Real, 0 < η ∧ EqOn R id (terminalCapBufferedProtectedHalfspace data i η)) ∧
              R '' ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) =
                data.toTerminalSaddleGeometry.flatten.symm ''
                  data.toTerminalSaddleGeometry.modelCaps i ∧
              ∃ S : Set E3, IsCompact S ∧
                ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
                  (∀ y ∉ S, G y = y) ∧ EqOn G id data.toTerminalSaddleGeometry.modelBand ∧
                  G '' (H '' data.toTerminalSaddleGeometry.C i) =
                    data.toTerminalSaddleGeometry.modelCaps i := by
  obtain ⟨E, hEheight, hEcore, hgerms, K, hK, F, hFfix, hFband, hFpoint, hFcap⟩ :=
    exists_prepared_horizontal_terminal_germs data hg Φ hzero hΦ hΦinv χ hχsmooth H
      hH hχ hplanar hlabels
  have hreplacements (i : Fin 3) : ∃ L : Set E3, IsCompact L ∧
      ∃ R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ L, R y = y) ∧ (∃ η : Real, 0 < η ∧ EqOn R id (terminalCapBufferedProtectedHalfspace data i η)) ∧
        R '' ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) =
          data.toTerminalSaddleGeometry.flatten.symm '' data.toTerminalSaddleGeometry.modelCaps i := by
    obtain ⟨U, hU, hrimU, _, hsurface⟩ := hgerms i
    cases hlabel : data.labels i with
    | inl j =>
      obtain ⟨L, hL, R, hRfix, hRhalf, hRcap⟩ := exists_buffered_prepared_terminal_lower_cap_replacement
        data hg Φ χ H hH hχ hplanar hlabels E F hEheight hEcore hFband hFpoint
        i j hlabel hU hrimU hsurface
      exact ⟨L, hL, R, hRfix,
        by simpa only [terminalCapBufferedProtectedHalfspace, hlabel] using hRhalf,
        by simpa only [hlabel] using hRcap⟩
    | inr j =>
      obtain ⟨L, hL, R, hRfix, hRhalf, hRcap⟩ := exists_buffered_prepared_terminal_upper_cap_replacement
        data hg Φ χ H hH hχ hplanar hlabels E F hEheight hEcore hFband hFpoint
        i j hlabel hU hrimU hsurface
      exact ⟨L, hL, R, hRfix,
        by simpa only [terminalCapBufferedProtectedHalfspace, hlabel] using hRhalf,
        by simpa only [hlabel] using hRcap⟩
  refine ⟨E, hEheight, hEcore, hgerms, K, hK, F, hFfix, hFband, hFpoint, hFcap, ?_⟩
  intro i
  obtain ⟨L, hL, R, hRfix, hRhalf, hRcap⟩ := hreplacements i
  obtain ⟨η, hη, hbuffer⟩ := hRhalf
  have hhalf : EqOn R id (terminalCapProtectedHalfspace data i) :=
    hbuffer.mono (terminalCapProtectedHalfspace_subset_buffered data i hη.le)
  exact ⟨L, hL, R, hRfix, ⟨η, hη, hbuffer⟩, hRcap,
    exists_flat_terminal_cap_replacement_of_prepared data i H E F R hK hL hFfix hFband
      (hFcap i) hRfix hhalf hRcap⟩

theorem exists_prepared_terminal_cap_replacements
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
      (∀ i, ∃ U : Set E3, IsOpen U ∧
        (fun y => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ''
          sphere (0 : E2) 1 ⊆ U ∧
        ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) ∩ U =
          (data.toTerminalSaddleGeometry.flatten.symm ''
            data.toTerminalSaddleGeometry.modelCaps i) ∩ U ∧
        (E '' range g) ∩ U =
          (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) ∩ U) ∧
      ∃ K : Set E3, IsCompact K ∧
        ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ y ∉ K, F y = y) ∧ EqOn F id data.toTerminalSaddleGeometry.modelBand ∧
          (∀ q : S2, F (H (data.toTerminalSaddleGeometry.flatten (g q))) =
            data.toTerminalSaddleGeometry.flatten (E (g q))) ∧
          (∀ i, F '' (H '' data.toTerminalSaddleGeometry.C i) =
            (data.toTerminalSaddleGeometry.flatten ∘ E ∘ g) ''
              terminalEndCap data.ends (data.labels i)) ∧
          ∀ i, ∃ L : Set E3, IsCompact L ∧
            ∃ R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
              (∀ y ∉ L, R y = y) ∧ EqOn R id (terminalCapProtectedHalfspace data i) ∧
              R '' ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) =
                data.toTerminalSaddleGeometry.flatten.symm ''
                  data.toTerminalSaddleGeometry.modelCaps i ∧
              ∃ S : Set E3, IsCompact S ∧
                ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
                  (∀ y ∉ S, G y = y) ∧ EqOn G id data.toTerminalSaddleGeometry.modelBand ∧
                  G '' (H '' data.toTerminalSaddleGeometry.C i) =
                    data.toTerminalSaddleGeometry.modelCaps i := by
  obtain ⟨E, hEh, hEc, hgerms, K, hK, F, hF, hFb, hFp, hFc, hr⟩ :=
    exists_buffered_prepared_terminal_cap_replacements data hg Φ hzero hΦ hΦinv χ
      hχsmooth H hH hχ hplanar hlabels
  refine ⟨E, hEh, hEc, hgerms, K, hK, F, hF, hFb, hFp, hFc, ?_⟩
  intro i
  obtain ⟨L, hL, R, hR, ⟨η, hη, hbuffer⟩, hi, hflat⟩ := hr i
  exact ⟨L, hL, R, hR,
    hbuffer.mono (terminalCapProtectedHalfspace_subset_buffered data i hη.le), hi, hflat⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
