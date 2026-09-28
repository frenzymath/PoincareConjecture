import PoincareConjecture.Proofs.M76.Brown.SpindleConjugation
import PoincareConjecture.Proofs.M76.Mathlib.ClosedExtension
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Compactness.LocallyCompact










set_option autoImplicit false

open Set

namespace BrownCollar

variable {B : Type*} [MetricSpace B] [LocallyCompactSpace B]





theorem exists_transition_adjustment
    (e : OpenPartialHomeomorph (B × Ico (0 : ℝ) 1) (B × Ico (0 : ℝ) 1))
    {W K : Set B} (hW : IsOpen W) (hK : IsCompact K) (hKW : K ⊆ W)
    (hsource : ∀ b ∈ W, collarBase b ∈ e.source)
    (hfixed : ∀ b ∈ W, e (collarBase b) = collarBase b) :
    ∃ N : Set (B × Ico (0 : ℝ) 1), IsCompact N ∧
      collarBase '' K ⊆ interior N ∧
      N ⊆ e.source ∩ (Prod.fst ⁻¹' W) ∧
      ∃ H : (B × Ico (0 : ℝ) 1) ≃ₜ (B × Ico (0 : ℝ) 1),
        (∀ z ∉ interior N, H z = z) ∧
        (∀ b, H (collarBase b) = collarBase b) ∧
        (∀ T, N ⊆ T → H ⁻¹' T = T) ∧
        ∃ V, IsOpen V ∧ collarBase '' K ⊆ V ∧ V ⊆ N ∧
          ∀ z ∈ V, e (H z) = z := by
  classical
  let : LocallyCompactSpace (Ico (0 : ℝ) 1) :=
    (show IsLocallyClosed (Ico (0 : ℝ) 1) from
      ⟨Iio 1, Ici 0, isOpen_Iio, isClosed_Ici, by
        ext t
        exact and_comm⟩).locallyCompactSpace
  have hbcont : Continuous (collarBase : B → B × Ico (0 : ℝ) 1) :=
    continuous_id.prodMk continuous_const
  obtain ⟨N, hN, hKN, hNSW⟩ := exists_compact_between (hK.image hbcont)
    (e.open_source.inter (hW.preimage continuous_fst)) (by
      rintro z ⟨b, hb, rfl⟩
      exact ⟨hsource b (hKW hb), hKW hb⟩)
  have hNS : N ⊆ e.source := hNSW.trans inter_subset_left
  let M := e '' N
  let f : N ≃ₜ M := e.homeomorphOfImageSubsetSource hNS rfl
  let O := interior N ∩ e '' interior N
  have hO : IsOpen O := isOpen_interior.inter
    (e.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hNS))
  have hKO : collarBase '' K ⊆ O := by
    rintro z ⟨b, hb, rfl⟩
    have hz := hKN ⟨b, hb, rfl⟩
    exact ⟨hz, ⟨collarBase b, hz, hfixed b (hKW hb)⟩⟩
  obtain ⟨U, hU, hKU, hUclosure⟩ := normal_exists_closure_subset hK.isClosed
    (hW.inter (hO.preimage hbcont)) (by
      intro b hb
      exact ⟨hKW hb, hKO ⟨b, hb, rfl⟩⟩)
  obtain ⟨height, hbounds, hpos, hAO⟩ := exists_spindleHeight hU hO
    (fun b hb => (hUclosure hb).2)
  have hAN : closure (spindle height) ⊆ N :=
    hAO.trans (fun _ hz => interior_subset hz.1)
  have hAM : closure (spindle height) ⊆ M := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := (hAO hz).2
    exact ⟨w, interior_subset hw, hwz⟩
  have hfbase (z : N) (hz : (z.val.2 : ℝ) = 0) :
      (f z : B × Ico (0 : ℝ) 1) = z := by
    have hzb : z.val = collarBase z.val.1 := Prod.ext rfl (Subtype.ext hz)
    change e z.val = z.val
    rw [hzb]
    exact hfixed z.val.1 (hNSW z.property).2
  obtain ⟨g, hgfix, hgoutside⟩ := exists_compact_spindle_conjugation
    height height.continuous hbounds hpos hN f hAN hAM
    (fun z _ hz => hfbase z hz)
  have hgfront (z : N) (hz : z.val ∈ frontier N) : g z = f z := by
    have hzint : z.val ∉ interior N :=
      (mem_frontier_iff_notMem_interior z.property).mp hz
    have hzA : z.val ∉ spindle height :=
      fun hzA => hzint (hAO (subset_closure hzA)).1
    apply hgoutside z hzA
    intro hfzA
    obtain ⟨w, hw, hfw⟩ := (hAO (subset_closure hfzA)).2
    have hwz : w = z.val := e.injOn (hNS (interior_subset hw)) (hNS z.property) hfw
    exact hzint (hwz ▸ hw)
  let k : N ≃ₜ N := g.trans f.symm
  have hkfront (z : N) (hz : z.val ∈ frontier N) : k z = z := by
    change f.symm (g z) = z
    rw [hgfront z hz, f.symm_apply_apply]
  let H := k.closedExtension hN.isClosed hkfront
  have hHmem {z : B × Ico (0 : ℝ) 1} (hz : z ∈ N) :
      H z = (k ⟨z, hz⟩ : B × Ico (0 : ℝ) 1) :=
    k.closedExtension_apply_mem hN.isClosed hkfront hz
  have hHoutside {z : B × Ico (0 : ℝ) 1} (hz : z ∉ N) : H z = z :=
    k.closedExtension_apply_notMem hN.isClosed hkfront hz
  have hHN (z : B × Ico (0 : ℝ) 1) : H z ∈ N ↔ z ∈ N := by
    by_cases hz : z ∈ N
    · exact iff_of_true (by rw [hHmem hz]; exact (k ⟨z, hz⟩).property) hz
    · rw [hHoutside hz]
  refine ⟨N, hN, hKN, hNSW, H, ?_, ?_, ?_, ?_⟩
  · intro z hz
    by_cases hzN : z ∈ N
    · exact k.closedExtension_apply_frontier hN.isClosed hkfront
        ((mem_frontier_iff_notMem_interior hzN).mpr hz)
    · exact hHoutside hzN
  · intro b
    by_cases hbN : collarBase b ∈ N
    · let z : N := ⟨collarBase b, hbN⟩
      have hfz : (f z : B × Ico (0 : ℝ) 1) = z := hfbase z rfl
      have hgf : g z = f z := by
        by_cases hb : 0 < height b
        · apply Subtype.ext
          calc
            (g z : B × Ico (0 : ℝ) 1) = z := hgfix z (subset_closure (by
              change 0 < height b / 2
              exact div_pos hb (by norm_num)))
            _ = f z := hfz.symm
        · have hzA : z.val ∉ spindle height := hb
          exact hgoutside z hzA (by simpa only [hfz] using hzA)
      rw [hHmem hbN]
      change (f.symm (g z) : B × Ico (0 : ℝ) 1) = collarBase b
      rw [hgf, f.symm_apply_apply]
    · exact hHoutside hbN
  · intro T hNT
    ext z
    by_cases hz : z ∈ N
    · exact iff_of_true (hNT ((hHN z).mpr hz)) (hNT hz)
    · change H z ∈ T ↔ z ∈ T
      rw [hHoutside hz]
  · let V := spindle (fun b => height b / 2)
    have hVN : V ⊆ N := by
      intro z hz
      apply hAN (subset_closure ?_)
      change (z.2 : ℝ) < height z.1 / 2 at hz
      change (z.2 : ℝ) < height z.1
      have hp := (hbounds z.1).1
      linarith
    refine ⟨V, isOpen_spindle _ (height.continuous.div_const 2), ?_, hVN, ?_⟩
    · rintro z ⟨b, hb, rfl⟩
      change 0 < height b / 2
      exact div_pos ((hpos b).mpr (hKU hb)) (by norm_num)
    · intro z hz
      rw [hHmem (hVN hz)]
      change (f (f.symm (g ⟨z, hVN hz⟩)) : B × Ico (0 : ℝ) 1) = z
      rw [f.apply_symm_apply]
      exact hgfix ⟨z, hVN hz⟩ (subset_closure hz)

end BrownCollar
