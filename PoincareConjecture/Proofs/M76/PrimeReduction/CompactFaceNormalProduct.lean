import PoincareConjecture.Proofs.M76.PrimeReduction.FaceNormalExtension
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialEmbeddedAffineImage
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option autoImplicit false

open Set Metric Topology

namespace Set

theorem IsCompact.exists_closed_normal_interval
    {Y : Type*} [TopologicalSpace Y] {D : Set Y} (hD : IsCompact D)
    {O : Set (Y × ℝ)} (hO : IsOpen O) (hzero : D ×ˢ {(0 : ℝ)} ⊆ O) :
    ∃ r : ℝ, 0 < r ∧ D ×ˢ Icc (-r) r ⊆ O := by
  obtain ⟨A, V, _, hV, hDA, h0V, hAV⟩ :=
    generalized_tube_lemma hD isCompact_singleton hO hzero
  obtain ⟨r, hr, hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hV.mem_nhds (h0V (mem_singleton (0 : ℝ))))
  refine ⟨r, hr, ?_⟩
  intro x hx
  apply hAV
  refine ⟨hDA hx.1, hrV ?_⟩
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le, mem_Icc] using hx.2

end Set

namespace OpenPartialHomeomorph

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X]

theorem exists_compact_face_normal_product
    (B : OpenPartialHomeomorph X E)
    (T : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    {D : Set (ℝ × ℝ)} (hD : IsCompact D)
    {U : Set X} (hU : IsOpen U)
    (hzero : ∀ z ∈ D, T (z, 0) ∈ B.target ∧ B.symm (T (z, 0)) ∈ U) :
    ∃ r : ℝ, 0 < r ∧
      MapsTo T (D ×ˢ Icc (-r) r) B.target ∧
      MapsTo (B.symm ∘ T) (D ×ˢ Icc (-r) r) U ∧
      ContinuousOn (B.symm ∘ T) (D ×ˢ Icc (-r) r) ∧
      InjOn (B.symm ∘ T) (D ×ˢ Icc (-r) r) ∧
      IsCompact ((B.symm ∘ T) '' (D ×ˢ Icc (-r) r)) ∧
      (∀ x ∈ D ×ˢ Icc (-r) r, T.symm (B (B.symm (T x))) = x) ∧
      ∀ x ∈ D ×ˢ Icc (-r) r,
        B.symm (T x) ∈ (B.symm ∘ T) '' (D ×ˢ {(0 : ℝ)}) ↔ x.2 = 0 := by
  let O : Set ((ℝ × ℝ) × ℝ) := T ⁻¹' (B '' (U ∩ B.source))
  have hO : IsOpen O :=
    (B.isOpen_image_of_subset_source (hU.inter B.open_source) inter_subset_right).preimage
      T.continuous
  have hDO : D ×ˢ {(0 : ℝ)} ⊆ O := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    have ht0 : t = 0 := mem_singleton_iff.mp ht
    subst t
    obtain ⟨hzt, hzU⟩ := hzero z hz
    exact ⟨B.symm (T (z, 0)), ⟨hzU, B.map_target hzt⟩, B.right_inv hzt⟩
  obtain ⟨r, hr, hprod⟩ := hD.exists_closed_normal_interval hO hDO
  have hT : MapsTo T (D ×ˢ Icc (-r) r) B.target := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hprod hx
    exact hyx ▸ B.mapsTo hy.2
  have hmap : MapsTo (B.symm ∘ T) (D ×ˢ Icc (-r) r) U := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hprod hx
    change B.symm (T x) ∈ U
    rw [← hyx, B.left_inv hy.2]
    exact hy.1
  have hc : ContinuousOn (B.symm ∘ T) (D ×ˢ Icc (-r) r) :=
    B.symm.continuousOn.comp T.continuous.continuousOn hT
  have hi : InjOn (B.symm ∘ T) (D ×ˢ Icc (-r) r) := by
    intro x hx y hy hxy
    exact T.injective (B.symm.injOn (hT hx) (hT hy) hxy)
  have h0r : (0 : ℝ) ∈ Icc (-r) r := ⟨by linarith, hr.le⟩
  refine ⟨r, hr, hT, hmap, hc, hi, (hD.prod isCompact_Icc).image_of_continuousOn hc,
    ?_, ?_⟩
  · intro x hx
    rw [B.right_inv (hT hx), T.symm_apply_apply]
  · intro x hx
    constructor
    · rintro ⟨y, hy, heq⟩
      have hy0 : y.2 = 0 := mem_singleton_iff.mp hy.2
      have hyprod : y ∈ D ×ˢ Icc (-r) r := ⟨hy.1, hy0 ▸ h0r⟩
      have hyx : y = x := hi hyprod hx heq
      exact hyx ▸ hy0
    · intro hx0
      exact ⟨x, ⟨hx.1, hx0⟩, rfl⟩

end OpenPartialHomeomorph
