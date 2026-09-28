import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverProper
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

def scalarPotentialStrip : Set Cover := {z | z.1 ∈ Ioo (0 : ℝ) 1}

def scalarNormalizedCover (H : Plane → ℝ) (V : Cover → ℝ) (P : ℝ)
    (hrange : ∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1) :
    scalarCoverStrip → scalarPotentialStrip :=
  fun z => ⟨scalarNormalizedCoverMap H V P z, hrange _ (scalarCoverMap_mem z.property)⟩

theorem scalarNormalizedCoverMap_deck {H : Plane → ℝ} {V : Cover → ℝ}
    {P : ℝ} (hP : P ≠ 0)
    (hdeck : ∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P)
    {z : Cover} (hz : z ∈ scalarCoverStrip) :
    scalarNormalizedCoverMap H V P (z + (0, 1)) =
      scalarNormalizedCoverMap H V P z + (0, 1) := by
  simp only [scalarNormalizedCoverMap, scalarCoverMap_periodic, hdeck z hz,
    Prod.mk_add_mk, add_zero, add_div, div_self hP]

theorem scalarNormalizedCover_isProperMap {H : Plane → ℝ}
    (hHc : Continuous H)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hrange : ∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1)
    {V : Cover → ℝ} (hVc : ContinuousOn V scalarCoverStrip) {P : ℝ} (hP : 0 < P)
    (hdeck : ∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P) :
    IsProperMap (scalarNormalizedCover H V P hrange) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  constructor
  · exact ((scalarNormalizedCoverMap_continuousOn hHc hVc P).domRestrict).subtype_mk _
  · intro K hK
    have himage : IsCompact ((Subtype.val : scalarPotentialStrip → Cover) '' K) :=
      hK.image continuous_subtype_val
    have htarget : (Subtype.val : scalarPotentialStrip → Cover) '' K ⊆
        {z : Cover | z.1 ∈ Ioo (0 : ℝ) 1} := by
      rintro z ⟨y, _, rfl⟩
      exact y.property
    have hc := scalarNormalizedCoverMap_compact_preimage hHc hinner houter hVc hP
      hdeck himage htarget
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert hc using 1
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, ⟨scalarNormalizedCover H V P hrange y, hy, rfl⟩⟩
    · rintro ⟨hz, y, hy, heq⟩
      refine ⟨⟨z, hz⟩, ?_, rfl⟩
      change scalarNormalizedCover H V P hrange ⟨z, hz⟩ ∈ K
      have hyEq : scalarNormalizedCover H V P hrange ⟨z, hz⟩ = y :=
        Subtype.ext heq.symm
      exact hyEq ▸ hy

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem exists_proper_annular_cover_conjugate :
    ∃ (H : Plane → ℝ) (V : Cover → ℝ) (P : ℝ),
      Continuous H ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus ∧
      (∀ x ∈ scalarAnnulus, D.laplacian H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 1 → H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 2 → H x = 1) ∧
      0 < P ∧ P = scalarFluxPeriod D H (3 / 2) ∧
      ContDiffOn ℝ ∞ V scalarCoverStrip ∧
      (∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z) ∧
      (∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P) ∧
      ∃ hrange : ∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1,
        IsProperMap (scalarNormalizedCover H V P hrange) := by
  obtain ⟨H, -, V, hHc, hHs, -, hlap, hinner, houter, hrange, hP, hVs, hdV, hdeck⟩ :=
    exists_positive_period_annular_cover_conjugate D
  exact ⟨H, V, scalarFluxPeriod D H (3 / 2), hHc, hHs, hlap, hinner, houter, hP, rfl,
    hVs, hdV, hdeck, hrange,
    scalarNormalizedCover_isProperMap hHc hinner houter hrange hVs.continuousOn hP hdeck⟩

end PoincareConjecture.M64Uniformization
