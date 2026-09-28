import PoincareConjecture.Proofs.M76.Rigidity.OriginalPrescribedBand
import PoincareConjecture.Proofs.M76.Rigidity.NormalizedParameterProduct
import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductOpenSubsets
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}

theorem OriginalDiskProduct.exists_marked_correction (P : OriginalDiskProduct e R j)
    (he : PLDomain e R)
    (hopenP : ∀ v : ℝ, 0 < v → v ≤ 1 →
      IsOpen ((Subtype.val : R → X) ⁻¹' (P.map '' (D ×ˢ Ioo (-v) v))))
    (F : E → X) (hF : PolyhedralPLInCharts e F (Q ×ˢ I))
    (hFi : InjOn F (Q ×ˢ I)) (hfront : MapsTo F (Q ×ˢ I) (frontier R))
    (hcenter : ∀ z ∈ Q, F (z, 0) = j z)
    (hopenF : IsOpen ((Subtype.val : frontier R → X) ⁻¹'
      (F '' (Q ×ˢ Ioo (-1 : ℝ) 1)))) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ ∃ P' : OriginalDiskProduct e R j,
      P'.map '' (D ×ˢ I) ⊆ P.map '' (D ×ˢ I) ∧
      (∀ z ∈ Q, ∀ t ∈ I, P'.map (z, t) = F (z, a * t)) ∧
      ∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : R → X) ⁻¹' (P'.map '' (D ×ˢ Ioo (-v) v))) := by
  obtain ⟨a, q, ha, hasmall, hq, hqi, hqm, hqc, _, hback, hqo⟩ :=
    P.exists_open_prescribed_band_lift he
      (hopenP (1 / 2) (by norm_num) (by norm_num)) F hF hFi hfront hcenter hopenF
  obtain ⟨f, hf, hfi, hfm, hfb, hfl, hfc, hfo⟩ :=
    exists_normalized_corrected_parameter_product ha q hq hqi hqm hqc hqo
  have hfclosed : MapsTo f (D ×ˢ I) (D ×ˢ I) :=
    fun z hz => ⟨(hfm hz).1, Ioo_subset_Icc_self (hfm hz).2⟩
  obtain ⟨K, hK, hKS⟩ := exists_finite_originalParameterPrism
  have hpoly : PolyhedralPLInCharts e (P.map ∘ f) (D ×ˢ I) := by
    have hfK : FinitePiecewiseAffineOn f K.space := hKS.symm ▸ hf
    have h := P.polyhedral.comp_finitePiecewiseAffineOn K hK hfK
      (fun z hz => hfclosed (hKS.subset hz))
    exact hKS ▸ h
  have hinj : InjOn (P.map ∘ f) (D ×ˢ I) := fun z hz w hw hzw =>
    hfi hz hw (P.injective (hfclosed hz) (hfclosed hw) hzw)
  let : CompactSpace (D ×ˢ I : Set E) :=
    isCompact_iff_compactSpace.mp ((isCompact_closedBall (0 : V2) 1).prod isCompact_Icc)
  let P' : OriginalDiskProduct e R j := {
    map := P.map ∘ f
    polyhedral := hpoly
    injective := hinj
    embedding := hpoly.continuousOn.domRestrict.isClosedEmbedding
      (fun z w hzw => Subtype.ext (hinj z.property w.property hzw))
    inside := P.inside.comp hfclosed
    central := by
      intro z hz
      change P.map (f (z, 0)) = j z
      rw [hfc z hz]
      exact P.central z hz
    proper := fun z hz => (P.proper (f z) (hfclosed hz)).trans (hfb z hz) }
  refine ⟨a, ha, hasmall, P', ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨f z, hfclosed hz, rfl⟩
  · intro z hz t ht
    change P.map (f (z, t)) = F (z, a * t)
    rw [hfl z hz t ht]
    apply hback (z, a * t)
    exact ⟨hz, by nlinarith [ht.1], by nlinarith [ht.2]⟩
  · intro v hv hvsmall
    have himage : f '' (D ×ˢ Ioo (-v) v) ⊆ D ×ˢ Ioo (-1 : ℝ) 1 := by
      rintro _ ⟨z, hz, rfl⟩
      apply hfm
      exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
    have hopen := P.isOpen_image_parameter_subset (hopenP 1 zero_lt_one le_rfl)
      himage (hfo v hv hvsmall)
    change IsOpen ((Subtype.val : R → X) ⁻¹' ((P.map ∘ f) '' (D ×ˢ Ioo (-v) v)))
    rw [Set.image_comp]
    exact hopen

end PoincareConjecture.M76
