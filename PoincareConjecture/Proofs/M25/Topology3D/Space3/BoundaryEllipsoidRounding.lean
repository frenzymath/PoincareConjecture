import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactTrackExtension
import PoincareConjecture.Proofs.M25.Topology3D.Space3.EllipsoidRounding
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BoundaryDiscFlow

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace NNReal

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem exists_compact_ellipsoid_rounding_field (A : E ≃L[ℝ] E)
    {S : Set E} (hS : IsCompact S) (hS0 : ∀ y ∈ S, y ≠ 0) :
    ∃ W : E → E, ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧
      ∃ k l : ℝ≥0, ∃ hk : LipschitzWith k W, ∃ hl : ∀ y, ‖W y‖ ≤ l,
        ∀ y ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
          boundedFlow W hk hl y t = ellipsoidRoundingTrack A t y := by
  obtain ⟨W, hW, hWc, _, k, l, hk, hl, htrack⟩ := exists_compact_field_tracking hS
    (ellipsoidRoundingTrack A)
    ((ellipsoidRoundingTrack_contDiffOn A).continuousOn.mono
      (fun p hp => ⟨mem_univ _, hS0 p.2 hp.2⟩))
    isClosed_singleton.isOpen_compl
    (fun t _ y hy => ellipsoidRoundingTrack_ne_zero A t (hS0 y hy))
    (ellipsoidRoundingField A) (ellipsoidRoundingField_contDiffOn A)
    (fun y _ t _ => ellipsoidRoundingTrack_hasDerivAt A y t)
  refine ⟨W, hW, hWc, k, l, hk, hl, ?_⟩
  intro y hy t ht
  simpa only [ellipsoidRoundingTrack_zero] using htrack y hy t ht

theorem exists_boundary_ellipsoid_rounding (v : E) (hv : ‖v‖ = 1)
    (A : (ℝ ∙ v)ᗮ ≃L[ℝ] (ℝ ∙ v)ᗮ)
    {S : Set ((ℝ ∙ v)ᗮ)} (hS : IsCompact S) (hS0 : ∀ y ∈ S, y ≠ 0) :
    ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (∀ y, ‖F y‖ = ‖y‖) ∧
      (∀ x ∈ S, F (stereoInvFun hv x : E) =
        (stereoInvFun hv (ellipsoidRoundingTrack A 1 x) : E)) ∧
      ∃ C : Set E, IsCompact C ∧ C ⊆ radialStereoTarget v ∧
        ∀ y, y ∉ C → F y = y := by
  obtain ⟨W, hW, hWc, k, l, hk, hl, htrack⟩ :=
    exists_compact_ellipsoid_rounding_field A hS hS0
  obtain ⟨Φ, _, _, hnorm, hΦtrack, C, hC, hCt, hfix⟩ :=
    exists_boundaryDisc_ambient_flow v hv W hW hWc hk hl
  refine ⟨Φ 1, hnorm 1, ?_, C, hC, hCt, hfix 1⟩
  intro x hx
  rw [hΦtrack, htrack x hx 1 ⟨zero_le_one, le_rfl⟩]

end PoincareConjecture.M25.Topology3D
