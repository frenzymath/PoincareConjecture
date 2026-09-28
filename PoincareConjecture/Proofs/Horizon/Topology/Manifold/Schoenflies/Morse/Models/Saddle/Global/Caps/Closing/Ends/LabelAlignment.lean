import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Terminal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.ModelDomain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Actual.TerminalNormalization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SaddleLevel SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

private theorem terminal_flatten_height (data : TerminalSaddleData M P p e) (y : E3) :
    data.toTerminalSaddleGeometry.flatten y 2 = inner Real (M.v : E3) y :=
  (data.frame_height (data.D y)).trans (data.D_height y)

private theorem terminal_actual_band_mem (data : TerminalSaddleData M P p e) (y : E3) :
    y ∈ data.toTerminalSaddleGeometry.actualBand ↔
      y ∈ data.toTerminalSaddleGeometry.flatten '' range g ∧
        y 2 ∈ data.toTerminalSaddleGeometry.I := by
  have hcoord : Saddle.toE3 (Saddle.toE2 y) (y 2) = y := by
    ext i
    fin_cases i <;> rfl
  simp only [TerminalSaddleGeometry.actualBand, mem_iUnion]
  constructor
  · rintro ⟨z, hz, hy, hyz⟩
    subst z
    exact ⟨hcoord ▸ hy, hz⟩
  · rintro ⟨hy, hz⟩
    exact ⟨y 2, hz, hcoord ▸ hy, rfl⟩

private theorem terminal_cap_band_domain (data : TerminalSaddleData M P p e) (i : Fin 3) :
    terminalEndCap data.ends (data.labels i) ∩
      {q | inner Real (M.v : E3) (g q) ∈ data.toTerminalSaddleGeometry.I} =
        range (terminalActualCutCircle data i) := by
  generalize hlabel : data.labels i = j
  rcases j with j | j
  · have hrim : terminalActualCutCircle data i = data.ends.lowerCutCircle j := by
      simp only [terminalActualCutCircle, hlabel]
    rw [hrim]
    ext q
    constructor
    · rintro ⟨hq, hh⟩
      rcases hq with hq | ⟨x, hx, rfl⟩
      · obtain ⟨⟨z, t⟩, ⟨_, ht⟩, rfl⟩ := hq
        have heq := (data.ends.lower j.1.1 j.1.2 j.2).actual_height z t ht
        have htcut : t = data.ends.lowerCut := by
          change data.ends.lowerCut ≤ _ ∧ _ ≤ data.ends.upperCut at hh
          rw [heq] at hh
          exact le_antisymm ht.2 hh.1
        exact ⟨z, by simp only [AnnularEndFamily.lowerCutCircle, htcut]⟩
      · have hout := data.ends.cap_height_outside_middle j.1.1 j.1.2 x hx
        change inner Real (M.v : E3) (g (j.1.1.chart x)) ∈ data.toTerminalSaddleGeometry.I at hh
        rw [j.1.1.parametrization_eq x hx] at hh
        exact False.elim (hout.elim (fun h => (not_lt_of_ge hh.1) h)
          (fun h => (not_lt_of_ge hh.2) h))
    · rintro ⟨z, rfl⟩
      refine ⟨Or.inl (data.ends.lowerCutCircle_mem_end j z), ?_⟩
      change data.ends.lowerCut ≤ _ ∧ _ ≤ data.ends.upperCut
      rw [data.ends.lowerCutCircle_height]
      exact ⟨le_rfl, data.ends.cuts_lt.le⟩
  · have hrim : terminalActualCutCircle data i = data.ends.upperCutCircle j := by
      simp only [terminalActualCutCircle, hlabel]
    rw [hrim]
    ext q
    constructor
    · rintro ⟨hq, hh⟩
      rcases hq with hq | ⟨x, hx, rfl⟩
      · change q ∈ (data.ends.upper j.1.1 j.1.2 j.2).region at hq
        rw [(data.ends.upper j.1.1 j.1.2 j.2).region_eq_image] at hq
        obtain ⟨⟨z, t⟩, ⟨_, ht⟩, rfl⟩ := hq
        have heq := (data.ends.upper j.1.1 j.1.2 j.2).actual_height z t ht
        have htcut : t = data.ends.upperCut := by
          change data.ends.lowerCut ≤ _ ∧ _ ≤ data.ends.upperCut at hh
          rw [heq] at hh
          exact le_antisymm hh.2 ht.1
        exact ⟨z, by simp only [AnnularEndFamily.upperCutCircle, htcut]⟩
      · have hout := data.ends.cap_height_outside_middle j.1.1 j.1.2 x hx
        change inner Real (M.v : E3) (g (j.1.1.chart x)) ∈ data.toTerminalSaddleGeometry.I at hh
        rw [j.1.1.parametrization_eq x hx] at hh
        exact False.elim (hout.elim (fun h => (not_lt_of_ge hh.1) h)
          (fun h => (not_lt_of_ge hh.2) h))
    · rintro ⟨z, rfl⟩
      refine ⟨Or.inl (data.ends.upperCutCircle_mem_end j z), ?_⟩
      change data.ends.lowerCut ≤ _ ∧ _ ≤ data.ends.upperCut
      rw [data.ends.upperCutCircle_height]
      exact ⟨data.ends.cuts_lt.le, le_rfl⟩

theorem terminal_actual_cutCircle_band_range (data : TerminalSaddleData M P p e) (i : Fin 3) :
    range (fun q : S1 => data.toTerminalSaddleGeometry.flatten
      (g (terminalActualCutCircle data i q))) =
        data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand := by
  change range ((data.toTerminalSaddleGeometry.flatten ∘ g) ∘ terminalActualCutCircle data i) = _
  rw [range_comp, ← terminal_cap_band_domain data i]
  ext y
  constructor
  · rintro ⟨q, ⟨hq, hh⟩, rfl⟩
    refine ⟨mem_image_of_mem _ hq, (terminal_actual_band_mem data _).mpr ⟨?_, ?_⟩⟩
    · exact mem_image_of_mem _ (mem_range_self q)
    · simpa only [Function.comp_def, mem_ofPred_eq, terminal_flatten_height] using hh
  · rintro ⟨⟨q, hq, rfl⟩, hh⟩
    refine ⟨q, ⟨hq, ?_⟩, rfl⟩
    simpa only [Function.comp_def, mem_ofPred_eq, terminal_flatten_height] using
      ((terminal_actual_band_mem data _).mp hh).2

variable (data : TerminalSaddleData M P p e)
  (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
  (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
  (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
  (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
  (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
    Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
  (hlabels : ∀ i, planarHeightMap Φ 1 ''
    (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
      data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)

include hH hχ hplanar hlabels

theorem terminal_labeled_cutCircle_range (i : Fin 3) :
    range (fun q : S1 => H (data.toTerminalSaddleGeometry.flatten
      (g (terminalActualCutCircle data i q)))) =
        range (fun q : S1 => data.toTerminalSaddleGeometry.flatten
          (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i q))) := by
  have h := terminal_cap_band_inter_image data Φ χ H hH hχ hplanar hlabels i
  rw [data.model_boundary i, ← terminal_band_image data Φ χ H hH hχ hplanar,
    ← image_inter (f := (H : E3 → E3)) H.injective,
    ← terminal_actual_cutCircle_band_range data i] at h
  rw [← range_comp] at h
  change (range fun q : S1 => H (data.toTerminalSaddleGeometry.flatten
    (g (terminalActualCutCircle data i q)))) = _ at h
  refine h.trans ?_
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, hq⟩, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, q.property, rfl⟩

theorem terminal_labeled_physical_cutCircle_range (i : Fin 3) :
    range (fun q : S1 => data.toTerminalSaddleGeometry.flatten.symm
      (H (data.toTerminalSaddleGeometry.flatten (g (terminalActualCutCircle data i q))))) =
        range (fun q : S1 => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i q)) := by
  have h := congrArg (fun s : Set E3 => data.toTerminalSaddleGeometry.flatten.symm '' s)
    (terminal_labeled_cutCircle_range data Φ χ H hH hχ hplanar hlabels i)
  simpa only [← range_comp, Function.comp_def, Diffeomorph.symm_apply_apply] using h

theorem terminal_labeled_model_rim_height (i : Fin 3) (x : E2)
    (hx : x ∈ sphere (0 : E2) 1) :
    inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x)) =
      match data.labels i with
      | .inl _ => data.ends.lowerCut
      | .inr _ => data.ends.upperCut := by
  have hm : data.toTerminalSaddleGeometry.flatten
      (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x)) ∈
        range (fun q : S1 => H (data.toTerminalSaddleGeometry.flatten
          (g (terminalActualCutCircle data i q)))) := by
    rw [terminal_labeled_cutCircle_range data Φ χ H hH hχ hplanar hlabels i]
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨q, hq⟩ := hm
  have hh := congrArg (fun y : E3 => y 2) hq
  dsimp only at hh
  rw [hH] at hh
  change data.toTerminalSaddleGeometry.flatten (g (terminalActualCutCircle data i q)) 2 =
    data.toTerminalSaddleGeometry.flatten
      (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x)) 2 at hh
  rw [terminal_flatten_height, terminal_flatten_height] at hh
  rw [← hh]
  generalize hlabel : data.labels i = j
  rcases j with j | j
  · simpa only [terminalActualCutCircle, hlabel] using data.ends.lowerCutCircle_height j q
  · simpa only [terminalActualCutCircle, hlabel] using data.ends.upperCutCircle_height j q

theorem terminal_labeled_model_lower_boundary (i : Fin 3) (j : data.ends.LowerCutIndex)
    (hlabel : data.labels i = Sum.inl j) :
    inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel (data.modelSeed i)) <
      data.ends.lowerCut ∧
    ∀ x ∈ sphere (0 : E2) 1,
      inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x)) =
        data.ends.lowerCut := by
  have hrim (x : E2) (hx : x ∈ sphere (0 : E2) 1) :
      inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x)) =
        data.ends.lowerCut := by
    simpa only [hlabel] using
      terminal_labeled_model_rim_height data Φ χ H hH hχ hplanar hlabels i x hx
  rcases terminal_model_domain_boundary data i with hl | hu
  · exact ⟨hl.1, hrim⟩
  · obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := E2) (x := 0)).mpr
      (show (0 : Real) ≤ 1 by norm_num)
    have hne := data.ends.cuts_lt.ne
    exact False.elim (hne ((hrim x hx).symm.trans (hu.2 x hx)))

theorem terminal_labeled_model_upper_boundary (i : Fin 3) (j : data.ends.UpperCutIndex)
    (hlabel : data.labels i = Sum.inr j) :
    data.ends.upperCut <
      inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel (data.modelSeed i)) ∧
    ∀ x ∈ sphere (0 : E2) 1,
      inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x)) =
        data.ends.upperCut := by
  have hrim (x : E2) (hx : x ∈ sphere (0 : E2) 1) :
      inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x)) =
        data.ends.upperCut := by
    simpa only [hlabel] using
      terminal_labeled_model_rim_height data Φ χ H hH hχ hplanar hlabels i x hx
  rcases terminal_model_domain_boundary data i with hl | hu
  · obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := E2) (x := 0)).mpr
      (show (0 : Real) ≤ 1 by norm_num)
    have hne := data.ends.cuts_lt.ne
    exact False.elim (hne ((hl.2 x hx).symm.trans (hrim x hx)))
  · exact ⟨hu.1, hrim⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
