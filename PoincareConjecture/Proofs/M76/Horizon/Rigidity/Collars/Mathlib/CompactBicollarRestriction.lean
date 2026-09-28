import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompactClosedStrip
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.InducedOpenImage

set_option autoImplicit false

open Set

namespace Poincare.Topology

theorem exists_compact_bicollar_restriction
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {A : Set E} (hA : IsCompact A) (c : E × ℝ → X)
    {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn c (A ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (A ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (hopen : IsOpen (c '' (A ×ˢ Ioo (-r) r)))
    {U : Set X} (hU : IsOpen U) (hzero : ∀ x ∈ A, c (x, 0) ∈ U) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ r / 2 ∧
      MapsTo c (A ×ˢ Icc (-delta) delta) U ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ delta → IsOpen (c '' (A ×ˢ Ioo (-eps) eps)) := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let f : A × Icc (-1 : ℝ) 1 → X := fun z => c ((z.1 : E), r * (z.2 : ℝ))
  have hf : Continuous f := by
    apply hc.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))
    intro z
    change ((z.1 : E), r * (z.2 : ℝ)) ∈ A ×ˢ Icc (-r) r
    refine ⟨z.1.property, ?_, ?_⟩ <;> nlinarith [z.2.property.1, z.2.property.2]
  have hfzero (x : A) : f (x, ⟨0, by norm_num⟩) ∈ U := by
    simpa only [f, mul_zero] using hzero x x.property
  obtain ⟨d, hd, hdhalf, hstrip⟩ := hf.exists_closed_strip_subset hU hfzero
  refine ⟨r * d, mul_pos hr hd, by nlinarith, ?_, ?_⟩
  · intro z hz
    have htd : |z.2 / r| ≤ d := by
      rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]
      exact abs_le.mpr ⟨by nlinarith [hz.2.1], by nlinarith [hz.2.2]⟩
    have htI : z.2 / r ∈ Icc (-1 : ℝ) 1 := by
      have ht := abs_le.mp htd
      constructor <;> linarith [ht.1, ht.2]
    have h := hstrip ⟨z.1, hz.1⟩ ⟨z.2 / r, htI⟩ htd
    change c (z.1, r * (z.2 / r)) ∈ U at h
    rwa [mul_div_cancel₀ _ hr.ne'] at h
  · intro eps heps hepsd
    have hepsr : eps ≤ r := by nlinarith
    let P : Set (E × ℝ) := A ×ˢ Icc (-r) r
    let time : P → ℝ := fun z => z.1.2
    let V : Set P := time ⁻¹' Ioo (-eps) eps
    let g : P → X := fun z => c z
    have hV : IsOpen V := isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val)
    have hVrange : g '' V ⊆ c '' (A ×ˢ Ioo (-r) r) := by
      rintro x ⟨z, hz, rfl⟩
      exact ⟨z, ⟨z.property.1, by linarith [hz.1], by linarith [hz.2]⟩, rfl⟩
    have hWrange : c '' (A ×ˢ Ioo (-r) r) ⊆ range g := by
      rintro x ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz.1, hz.2.1.le, hz.2.2.le⟩, rfl⟩
    have himage : g '' V = c '' (A ×ˢ Ioo (-eps) eps) := by
      apply Subset.antisymm
      · rintro x ⟨z, hz, rfl⟩
        exact ⟨z, ⟨z.property.1, hz⟩, rfl⟩
      · rintro x ⟨z, hz, rfl⟩
        refine ⟨⟨z, hz.1, ?_, ?_⟩, hz.2, rfl⟩ <;> linarith [hz.2.1, hz.2.2]
    rw [← himage]
    exact hi.isInducing.isOpen_image_of_subset_open hV hopen hVrange hWrange

end Poincare.Topology
