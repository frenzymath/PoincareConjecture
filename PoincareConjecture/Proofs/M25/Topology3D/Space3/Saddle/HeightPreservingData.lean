import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightTubeTransport

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞

noncomputable def SurgeryCapTag.mapHeightPreserving
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (C : SurgeryCapTag psi u) (K : D3)
    (hK : ∀ y : E3, ⟪(u : E3), K y⟫_ℝ = ⟪(u : E3), y⟫_ℝ) :
    SurgeryCapTag (fun p => K (psi p)) u := by
  let id1 := Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞
  exact {
    profile := C.profile
    cutHeight := C.cutHeight
    removal := C.removal
    scale := C.scale
    sign := C.sign
    removal_pos := C.removal_pos
    scale_pos := C.scale_pos
    sign_abs := C.sign_abs
    scale_small := C.scale_small
    tube := heightTransportTube C.tube id1 K
    tube_source := heightTransportTube_closedDisc_source C.tube id1 K C.tube_source
    tube_smooth := heightTransportTube_contDiffOn C.tube id1 K C.tube_smooth
    tube_inverse := heightTransportTube_contDiffOn_symm C.tube id1 K C.tube_inverse
    tube_height := heightTransportTube_height C.tube id1 K u u C.tube_height hK
    sourceChart := C.sourceChart
    source_smooth := C.source_smooth
    source_inverse := C.source_inverse
    overlapWidth := C.overlapWidth
    overlap_pos := C.overlap_pos
    overlap_le := C.overlap_le
    source_band := C.source_band
    central_eq := fun q hq => congrArg K (C.central_eq q hq)
    flatChart := C.flatChart
    flat_source := C.flat_source
    flat_smooth := C.flat_smooth
    flat_inverse := C.flat_inverse
    flat_eq := C.flat_eq
    beta := C.beta
    beta_ne := C.beta_ne
    collarWidth := C.collarWidth
    collar_pos := C.collar_pos
    collar_le := C.collar_le
    collar_eq := fun x hx s hs => congrArg K (C.collar_eq x hx s hs) }

theorem SurgeryCapTag.mapHeightPreserving_geometry
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (C : SurgeryCapTag psi u) (K : D3)
    (hK : ∀ y : E3, ⟪(u : E3), K y⟫_ℝ = ⟪(u : E3), y⟫_ℝ) :
    let C' := C.mapHeightPreserving K hK
    C'.profile = C.profile ∧ C'.cutHeight = C.cutHeight ∧
    C'.removal = C.removal ∧ C'.scale = C.scale ∧ C'.sign = C.sign ∧
    C'.sourceChart = C.sourceChart ∧ C'.overlapWidth = C.overlapWidth ∧
    C'.flatChart = C.flatChart ∧ C'.beta = C.beta ∧ C'.collarWidth = C.collarWidth ∧
    C'.tube = heightTransportTube C.tube (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞) K ∧
    (∀ p : E2 × ℝ, C'.tube p = K (C.tube p)) ∧
    (∀ y : E3, C'.tube.symm y = C.tube.symm (K.symm y)) ∧
    C'.tube.source = C.tube.source ∧ C'.tube.target = K '' C.tube.target ∧
    (∀ A : Set (E2 × ℝ), C'.tube '' A = K '' (C.tube '' A)) ∧
    (∀ q : UnitTwoSphere,
      C'.profile.capMap C'.tube C'.cutHeight C'.sign C'.removal C'.scale q =
        K (C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q)) ∧
    C'.sourceCap = C.sourceCap ∧ C'.sourceSeam = C.sourceSeam ∧
    C'.cap = K '' C.cap ∧ C'.seam = K '' C.seam := by
  let id1 := Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, fun _ => rfl, rfl, rfl, ?_, ?_⟩
  · ext p
    exact heightTransportTube_mem_source C.tube id1 K p
  · ext y
    change y ∈ (heightTransportTube C.tube id1 K).target ↔ y ∈ K '' C.tube.target
    rw [heightTransportTube_mem_target]
    constructor
    · intro hy
      exact ⟨K.symm y, hy, K.apply_symm_apply y⟩
    · rintro ⟨v, hv, rfl⟩
      simpa only [Diffeomorph.symm_apply_apply] using hv
  · intro A
    exact (image_image K C.tube A).symm
  · exact (image_image K (fun q : UnitTwoSphere => psi (q, 0)) C.sourceCap).symm
  · exact (image_image K (fun q : UnitTwoSphere => psi (q, 0)) C.sourceSeam).symm

noncomputable def SaddlePieceData.mapHeightPreserving
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (D : SaddlePieceData psi u) (K : D3)
    (hK : ∀ y : E3, ⟪(u : E3), K y⟫_ℝ = ⟪(u : E3), y⟫_ℝ) :
    SaddlePieceData (fun p => K (psi p)) u := by
  have hfun : (fun p : UnitTwoSphere => ⟪(u : E3), K (psi (p, 0))⟫_ℝ) =
      (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) := funext (fun p => hK (psi (p, 0)))
  exact {
    capCount := D.capCount
    cap := fun i => (D.cap i).mapHeightPreserving K hK
    sourceCore := D.sourceCore
    sourceCore_compact := D.sourceCore_compact
    sourceCore_connected := D.sourceCore_connected
    source_cover := D.source_cover
    source_incidence := D.source_incidence
    sourceCap_disjoint := D.sourceCap_disjoint
    point := D.point
    slabLower := D.slabLower
    slabUpper := D.slabUpper
    core_in_slab := by simpa only [hK] using D.core_in_slab
    point_in_slab := by simpa only [hK] using D.point_in_slab
    unique_critical := by rw [hfun]; exact D.unique_critical
    morse := D.morse
    morse_smooth := D.morse_smooth
    morse_inverse := D.morse_inverse
    morse_point := D.morse_point
    morseSign1 := D.morseSign1
    morseSign2 := D.morseSign2
    morseSign1_sq := D.morseSign1_sq
    morseSigns_opposite := D.morseSigns_opposite
    morse_height := by simpa only [hK] using D.morse_height
    protectedSet := D.protectedSet
    protected_open := D.protected_open
    point_mem_protected := D.point_mem_protected
    protected_closure := D.protected_closure
    cutRadius := D.cutRadius
    removal_lt_cutRadius := D.removal_lt_cutRadius
    cutRadius_lt_gap := by
      intro i
      change D.cutRadius i < |(D.cap i).cutHeight - ⟪(u : E3), K (psi (D.point, 0))⟫_ℝ|
      rw [hK]
      exact D.cutRadius_lt_gap i
    cut_side := by
      intro i
      change ((D.cap i).sign = 1 ∧ (D.cap i).cutHeight < ⟪(u : E3), K (psi (D.point, 0))⟫_ℝ) ∨
        ((D.cap i).sign = -1 ∧ ⟪(u : E3), K (psi (D.point, 0))⟫_ℝ < (D.cap i).cutHeight)
      rw [hK]
      exact D.cut_side i }

theorem SaddlePieceData.mapHeightPreserving_geometry
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (D : SaddlePieceData psi u) (K : D3)
    (hK : ∀ y : E3, ⟪(u : E3), K y⟫_ℝ = ⟪(u : E3), y⟫_ℝ) :
    let D' := D.mapHeightPreserving K hK
    D'.capCount = D.capCount ∧
    (∀ i : Fin D.capCount, D'.cap i = (D.cap i).mapHeightPreserving K hK) ∧
    D'.sourceCore = D.sourceCore ∧ D'.point = D.point ∧
    D'.slabLower = D.slabLower ∧ D'.slabUpper = D.slabUpper ∧
    D'.morse = D.morse ∧ D'.morseSign1 = D.morseSign1 ∧
    D'.morseSign2 = D.morseSign2 ∧ D'.protectedSet = D.protectedSet ∧
    D'.cutRadius = D.cutRadius ∧
    (∀ i : Fin D.capCount,
      (D'.cap i).tube ''
        (closedBall (0 : E2) 1 ×ˢ closedBall (D'.cap i).cutHeight (D'.cutRadius i)) =
      K '' ((D.cap i).tube ''
        (closedBall (0 : E2) 1 ×ˢ closedBall (D.cap i).cutHeight (D.cutRadius i)))) := by
  refine ⟨rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro i
  exact (image_image K (D.cap i).tube _).symm

end PoincareConjecture.M25.Topology3D
