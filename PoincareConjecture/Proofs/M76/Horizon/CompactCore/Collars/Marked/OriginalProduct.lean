import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.ClosedSheets
import PoincareConjecture.Proofs.M76.Rigidity.OriginalMarkedProductCorrection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Rescaling







set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

open Dehn.Annuli.RimBands

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1



theorem OriginalDiskProduct.exists_sheet_preserving_correction
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S T : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (he : PLDomain e R)
    (hopenP : ∀ v : ℝ, 0 < v → v ≤ 1 →
      IsOpen ((Subtype.val : R → X) ⁻¹' (P.map '' (Disk ×ˢ Ioo (-v) v))))
    {F : (V2 × ℝ) → X} (hF : PolyhedralPLInCharts e F (Rim ×ˢ I))
    (hFi : InjOn F (Rim ×ˢ I)) (hfront : MapsTo F (Rim ×ˢ I) (frontier R))
    (hcenter : ∀ z ∈ Rim, F (z, 0) = j z)
    (hopenF : IsOpen ((Subtype.val : frontier R → X) ⁻¹'
      (F '' (Rim ×ˢ Ioo (-1 : ℝ) 1))))
    (hS : IsClosed S) (hT : IsClosed T) (hcover : frontier R ⊆ S ∪ T)
    {U : Set Rim} (hU : IsOpen U) (hseam : ∀ z : Rim, j z ∈ S ∩ T → z ∈ U)
    {r : ℝ} (hr : 0 < r)
    (hlocal : ∀ z ∈ U, ∀ t ∈ I, |t| ≤ r →
      (F ((z : V2), t) ∈ S ∩ T ↔ j z ∈ S ∩ T)) :
    ∃ P' : OriginalDiskProduct e R j,
      P'.map '' (Disk ×ˢ I) ⊆ P.map '' (Disk ×ˢ I) ∧
      (∀ z ∈ Rim, ∀ t ∈ I,
        (P'.map (z, t) ∈ S ↔ j z ∈ S) ∧ (P'.map (z, t) ∈ T ↔ j z ∈ T)) ∧
      ∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : R → X) ⁻¹' (P'.map '' (Disk ×ˢ Ioo (-v) v))) := by
  let f : Rim × I → X := fun p => F (p.1, p.2)
  have hf : Continuous f := hF.continuousOn.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)) (fun p => ⟨p.1.property, p.2.property⟩)
  let : CompactSpace Rim := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V2) 1)
  have hc (z : Rim) : f (z, ⟨0, by norm_num⟩) = j z := hcenter z z.property
  obtain ⟨δ, hδ, hδsmall, _, hmarked⟩ :=
    exists_closed_strip_preserving_closed_sheets hf hS hT
      (fun p => hcover (hfront ⟨p.1.property, p.2.property⟩)) hU
      (fun z hz => hseam z ((hc z) ▸ hz)) hr (by
        intro z hz t ht
        simpa only [hc z] using hlocal z hz t t.property ht)
  obtain ⟨hG, hGi, hGfront, hGc, hGo⟩ :=
    rescaled_boundary_band_properties hF hFi hfront hcenter hopenF hδ (by linarith)
  obtain ⟨a, ha, hasmall, P', himage, hboundary, hopen⟩ :=
    P.exists_marked_correction he hopenP (F ∘ bandTimeScale δ) hG hGi hGfront hGc hGo
  refine ⟨P', himage, ?_, hopen⟩
  intro z hz t ht
  rw [hboundary z hz t ht]
  have habs : |a * t| ≤ 1 := abs_le.mpr ⟨by nlinarith [ht.1, ht.2],
    by nlinarith [ht.1, ht.2]⟩
  have hscaled : |δ * (a * t)| ≤ δ := by
    rw [abs_mul, abs_of_pos hδ]
    exact (mul_le_mul_of_nonneg_left habs hδ.le).trans_eq (mul_one δ)
  have hI : δ * (a * t) ∈ I := by
    obtain ⟨hl, hu⟩ := abs_le.mp hscaled
    exact ⟨by linarith, by linarith⟩
  simpa only [f, hc, Function.comp_apply, bandTimeScale_apply] using
    hmarked ⟨z, hz⟩ ⟨δ * (a * t), hI⟩ hscaled

end PoincareConjecture.M76
