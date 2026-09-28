import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlatCapProfile
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapEmbedding

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

structure SurgeryCapProfile where
  horizontal : ℝ → ℝ
  vertical : E2 → ℝ
  horizontal_smooth : ContDiff ℝ ∞ horizontal
  vertical_smooth : ContDiff ℝ ∞ vertical
  horizontal_pos : ∀ z, 0 < horizontal z
  vertical_pos : ∀ x, 0 < vertical x
  horizontal_near : ∀ z, |z| ≤ 1 / 4 →
    horizontal z = (Real.sqrt (1 - z ^ 2))⁻¹
  horizontal_far : ∀ z, 1 / 2 ≤ |z| → horizontal z = 1
  horizontal_bound : ∀ z, |z| < 1 →
    horizontal z ≤ (Real.sqrt (1 - z ^ 2))⁻¹
  vertical_near : ∀ x, ‖x‖ ≤ 1 / 4 →
    vertical x = (Real.sqrt (1 - ‖x‖ ^ 2))⁻¹
  vertical_far : ∀ x, 1 / 2 ≤ ‖x‖ → vertical x = 1
  heightBound : ℝ
  one_le_heightBound : 1 ≤ heightBound
  height_bound : ∀ q : UnitTwoSphere,
    |(surgeryCapModel horizontal vertical horizontal_smooth vertical_smooth
      (fun z => (horizontal_pos z).ne') (fun x => (vertical_pos x).ne') q).2| ≤
        heightBound

theorem exists_surgery_cap_profile : Nonempty SurgeryCapProfile := by
  obtain ⟨a, ha, ha1, hanear, hafar, habound⟩ :=
    exists_bounded_flatCap_profile (E := ℝ)
  obtain ⟨b, hb, hbpos, hbnear, hbfar⟩ := exists_flatCap_profile (E := E2)
  have hapos : ∀ z, 0 < a z := fun z => lt_of_lt_of_le zero_lt_one (ha1 z)
  obtain ⟨M, hM1, hM⟩ := surgeryCapModel_exists_height_bound a b ha hb
    (fun z => (hapos z).ne') (fun x => (hbpos x).ne')
  refine ⟨{
    horizontal := a
    vertical := b
    horizontal_smooth := ha
    vertical_smooth := hb
    horizontal_pos := hapos
    vertical_pos := hbpos
    horizontal_near := ?_
    horizontal_far := ?_
    horizontal_bound := ?_
    vertical_near := hbnear
    vertical_far := hbfar
    heightBound := M
    one_le_heightBound := hM1
    height_bound := hM }⟩
  · intro z hz
    simpa only [Real.norm_eq_abs, sq_abs] using
      hanear z (by simpa only [Real.norm_eq_abs] using hz)
  · intro z hz
    exact hafar z (by simpa only [Real.norm_eq_abs] using hz)
  · intro z hz
    simpa only [Real.norm_eq_abs, sq_abs] using
      habound z (by simpa only [Real.norm_eq_abs] using hz)

namespace SurgeryCapProfile

noncomputable def model (P : SurgeryCapProfile) : UnitTwoSphere → E2 × ℝ :=
  surgeryCapModel P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')

theorem model_eq (P : SurgeryCapProfile) :
    P.model = surgeryCapModel P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne') := rfl

theorem model_contMDiff (P : SurgeryCapProfile) :
    ContMDiff (𝓡 2) 𝓘(ℝ, E2 × ℝ) ∞ P.model :=
  surgeryCapModel_contMDiff P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')

theorem model_fst_norm_le (P : SurgeryCapProfile) (q : UnitTwoSphere) :
    ‖(P.model q).1‖ ≤ 1 :=
  surgeryCapModel_fst_norm_le P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
    P.horizontal_pos P.horizontal_bound q

noncomputable def capMap (P : SurgeryCapProfile)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3) (t sigma c l : ℝ) :
    UnitTwoSphere → E3 :=
  surgeryCapMap P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne') T t sigma c l

@[simp] theorem capMap_apply (P : SurgeryCapProfile)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3) (t sigma c l : ℝ) (q : UnitTwoSphere) :
    P.capMap T t sigma c l q = T ((P.model q).1, t + sigma * (c + l * (P.model q).2)) := rfl

theorem capMap_contMDiff (P : SurgeryCapProfile)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall 0 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source) (t sigma c l : ℝ) :
    ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ (P.capMap T t sigma c l) :=
  surgeryCapMap_contMDiff P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
    P.horizontal_pos P.horizontal_bound T hsource hT t sigma c l

end SurgeryCapProfile

structure SurgeryCapTag (ψ : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere) where
  profile : SurgeryCapProfile
  cutHeight : ℝ
  removal : ℝ
  scale : ℝ
  sign : ℝ
  removal_pos : 0 < removal
  scale_pos : 0 < scale
  sign_abs : |sign| = 1
  scale_small : scale * profile.heightBound < removal / 4
  tube : OpenPartialHomeomorph (E2 × ℝ) E3
  tube_source : closedBall 0 1 ×ˢ (univ : Set ℝ) ⊆ tube.source
  tube_smooth : ContDiffOn ℝ ∞ tube tube.source
  tube_inverse : ContDiffOn ℝ ∞ tube.symm tube.target
  tube_height : ∀ p ∈ tube.source, ⟪(u : E3), tube p⟫_ℝ = p.2
  sourceChart : OpenPartialHomeomorph UnitTwoSphere UnitTwoSphere
  source_smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ sourceChart sourceChart.source
  source_inverse : ContMDiffOn (𝓡 2) (𝓡 2) ∞ sourceChart.symm sourceChart.target
  overlapWidth : ℝ
  overlap_pos : 0 < overlapWidth
  overlap_le : overlapWidth ≤ 1 / 4
  source_band : ∀ q : UnitTwoSphere,
    (heightCoordinates (q : E3)).2 < overlapWidth → q ∈ sourceChart.source
  central_eq : ∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 < overlapWidth →
    ψ (sourceChart q, 0) = profile.capMap tube cutHeight sign removal scale q
  flatChart : OpenPartialHomeomorph E2 UnitTwoSphere
  flat_source : closedBall 0 (1 / 4) ⊆ flatChart.source
  flat_smooth : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ flatChart flatChart.source
  flat_inverse : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ flatChart.symm flatChart.target
  flat_eq : ∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 ≤ 0 →
    ‖(heightCoordinates (q : E3)).1‖ ≤ 1 / 4 →
      flatChart (heightCoordinates (q : E3)).1 = sourceChart q
  beta : ℝ
  beta_ne : beta ≠ 0
  collarWidth : ℝ
  collar_pos : 0 < collarWidth
  collar_le : collarWidth ≤ 1
  collar_eq : ∀ x : E2, ‖x‖ ≤ 1 / 8 → ∀ s : ℝ, |s| < collarWidth →
    ψ (flatChart x, s) = tube (x, cutHeight + sign * (removal - scale) + beta * s)

namespace SurgeryCapTag

variable {ψ : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}

def sourceCap (C : SurgeryCapTag ψ u) : Set UnitTwoSphere :=
  C.sourceChart '' {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}

def sourceSeam (C : SurgeryCapTag ψ u) : Set UnitTwoSphere :=
  C.sourceChart '' {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 = 0}

def cap (C : SurgeryCapTag ψ u) : Set E3 :=
  (fun q : UnitTwoSphere => ψ (q, 0)) '' C.sourceCap

def seam (C : SurgeryCapTag ψ u) : Set E3 :=
  (fun q : UnitTwoSphere => ψ (q, 0)) '' C.sourceSeam

theorem south_mem_source (C : SurgeryCapTag ψ u) (q : UnitTwoSphere)
    (hq : (heightCoordinates (q : E3)).2 ≤ 0) : q ∈ C.sourceChart.source :=
  C.source_band q (lt_of_le_of_lt hq C.overlap_pos)

theorem cap_eq_image (C : SurgeryCapTag ψ u) :
    C.cap = C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} := by
  change (fun q : UnitTwoSphere => ψ (q, 0)) ''
    (C.sourceChart '' {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}) = _
  rw [image_image]
  apply image_congr
  intro q hq
  exact C.central_eq q (lt_of_le_of_lt hq C.overlap_pos)

theorem seam_eq_image (C : SurgeryCapTag ψ u) :
    C.seam = C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 = 0} := by
  change (fun q : UnitTwoSphere => ψ (q, 0)) ''
    (C.sourceChart '' {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 = 0}) = _
  rw [image_image]
  apply image_congr
  intro q hq
  exact C.central_eq q (by rw [hq]; exact C.overlap_pos)

theorem sourceCap_isCompact (C : SurgeryCapTag ψ u) : IsCompact C.sourceCap := by
  have hh : Continuous (fun q : UnitTwoSphere => (heightCoordinates (q : E3)).2) :=
    (heightCoordinates.continuous.comp continuous_subtype_val).snd
  exact (isClosed_le hh continuous_const).isCompact.image_of_continuousOn
    (C.sourceChart.continuousOn.mono (fun q hq => C.south_mem_source q hq))

theorem sourceSeam_isCompact (C : SurgeryCapTag ψ u) : IsCompact C.sourceSeam := by
  have hh : Continuous (fun q : UnitTwoSphere => (heightCoordinates (q : E3)).2) :=
    (heightCoordinates.continuous.comp continuous_subtype_val).snd
  exact (isClosed_eq hh continuous_const).isCompact.image_of_continuousOn
    (C.sourceChart.continuousOn.mono (fun q hq => C.south_mem_source q hq.le))

theorem cap_isCompact (C : SurgeryCapTag ψ u) : IsCompact C.cap := by
  rw [C.cap_eq_image]
  have hh : Continuous (fun q : UnitTwoSphere => (heightCoordinates (q : E3)).2) :=
    (heightCoordinates.continuous.comp continuous_subtype_val).snd
  exact (isClosed_le hh continuous_const).isCompact.image
    (C.profile.capMap_contMDiff C.tube C.tube_source C.tube_smooth
      C.cutHeight C.sign C.removal C.scale).continuous

theorem seam_isCompact (C : SurgeryCapTag ψ u) : IsCompact C.seam := by
  rw [C.seam_eq_image]
  have hh : Continuous (fun q : UnitTwoSphere => (heightCoordinates (q : E3)).2) :=
    (heightCoordinates.continuous.comp continuous_subtype_val).snd
  exact (isClosed_eq hh continuous_const).isCompact.image
    (C.profile.capMap_contMDiff C.tube C.tube_source C.tube_smooth
      C.cutHeight C.sign C.removal C.scale).continuous

end SurgeryCapTag

end PoincareConjecture.M25.Topology3D
