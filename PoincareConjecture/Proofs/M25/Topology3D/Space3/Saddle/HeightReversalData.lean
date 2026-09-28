import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightTubeTransport












set_option autoImplicit false

open Set
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {ψ : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}



noncomputable def SurgeryCapTag.reverseHeight (C : SurgeryCapTag ψ u) :
    SurgeryCapTag ψ (-u) := by
  let n := (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).toDiffeomorph
  let g := Diffeomorph.refl 𝓘(ℝ, E3) E3 ∞
  exact {
    profile := C.profile
    cutHeight := -C.cutHeight
    removal := C.removal
    scale := C.scale
    sign := -C.sign
    removal_pos := C.removal_pos
    scale_pos := C.scale_pos
    sign_abs := by simpa only [abs_neg] using C.sign_abs
    scale_small := C.scale_small
    tube := heightTransportTube C.tube n g
    tube_source := heightTransportTube_closedDisc_source C.tube n g C.tube_source
    tube_smooth := heightTransportTube_contDiffOn C.tube n g C.tube_smooth
    tube_inverse := heightTransportTube_contDiffOn_symm C.tube n g C.tube_inverse
    tube_height := by
      apply heightTransportTube_height C.tube n g u (-u) C.tube_height
      intro y
      change ⟪((-u : UnitTwoSphere) : E3), y⟫_ℝ = -⟪(u : E3), y⟫_ℝ
      rw [coe_neg_sphere, inner_neg_left]
    sourceChart := C.sourceChart
    source_smooth := C.source_smooth
    source_inverse := C.source_inverse
    overlapWidth := C.overlapWidth
    overlap_pos := C.overlap_pos
    overlap_le := C.overlap_le
    source_band := C.source_band
    central_eq := by
      intro q hq
      change ψ (C.sourceChart q, 0) = C.tube ((C.profile.model q).1,
        -(-C.cutHeight + -C.sign * (C.removal + C.scale * (C.profile.model q).2)))
      rw [C.central_eq q hq, SurgeryCapProfile.capMap_apply]
      congr 1
      apply Prod.ext
      · rfl
      · ring
    flatChart := C.flatChart
    flat_source := C.flat_source
    flat_smooth := C.flat_smooth
    flat_inverse := C.flat_inverse
    flat_eq := C.flat_eq
    beta := -C.beta
    beta_ne := neg_ne_zero.mpr C.beta_ne
    collarWidth := C.collarWidth
    collar_pos := C.collar_pos
    collar_le := C.collar_le
    collar_eq := by
      intro x hx s hs
      change ψ (C.flatChart x, s) = C.tube
        (x, -(-C.cutHeight + -C.sign * (C.removal - C.scale) + -C.beta * s))
      rw [C.collar_eq x hx s hs]
      congr 1
      apply Prod.ext
      · rfl
      · ring }



theorem SurgeryCapTag.reverseHeight_tube (C : SurgeryCapTag ψ u) :
    (∀ p : E2 × ℝ, C.reverseHeight.tube p = C.tube (p.1, -p.2)) ∧
      (∀ y : E3, C.reverseHeight.tube.symm y =
        ((C.tube.symm y).1, -(C.tube.symm y).2)) ∧
      C.reverseHeight.tube.source = {p | (p.1, -p.2) ∈ C.tube.source} ∧
      C.reverseHeight.tube.target = C.tube.target := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · ext p
    exact heightTransportTube_mem_source C.tube _ _ p
  · ext y
    exact heightTransportTube_mem_target C.tube _ _ y



theorem SurgeryCapTag.reverseHeight_sets (C : SurgeryCapTag ψ u) :
    C.reverseHeight.sourceCap = C.sourceCap ∧
      C.reverseHeight.sourceSeam = C.sourceSeam ∧
      C.reverseHeight.cap = C.cap ∧ C.reverseHeight.seam = C.seam :=
  ⟨rfl, rfl, rfl, rfl⟩



noncomputable def SaddlePieceData.reverseHeight (D : SaddlePieceData ψ u) :
    SaddlePieceData ψ (-u) := by
  exact {
    capCount := D.capCount
    cap := fun i => (D.cap i).reverseHeight
    sourceCore := D.sourceCore
    sourceCore_compact := D.sourceCore_compact
    sourceCore_connected := D.sourceCore_connected
    source_cover := D.source_cover
    source_incidence := D.source_incidence
    sourceCap_disjoint := D.sourceCap_disjoint
    point := D.point
    slabLower := -D.slabUpper
    slabUpper := -D.slabLower
    core_in_slab := by
      rintro y ⟨q, hq, rfl⟩
      have h := D.core_in_slab ⟨q, hq, rfl⟩
      simp only [coe_neg_sphere, inner_neg_left]
      exact ⟨neg_le_neg h.2, neg_le_neg h.1⟩
    point_in_slab := by
      simp only [coe_neg_sphere, inner_neg_left]
      exact ⟨neg_lt_neg D.point_in_slab.2, neg_lt_neg D.point_in_slab.1⟩
    unique_critical := by
      intro q hq
      have hf : (fun p : UnitTwoSphere => ⟪((-u : UnitTwoSphere) : E3), ψ (p, 0)⟫_ℝ) =
          -(fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) := by
        funext p
        simp only [Pi.neg_apply, coe_neg_sphere, inner_neg_left]
      change (mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪((-u : UnitTwoSphere) : E3), ψ (p, 0)⟫_ℝ) q :
          TangentSpace (𝓡 2) q →L[ℝ] ℝ) = 0 ↔ q = D.point
      rw [hf, mfderiv_neg]
      change -(mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), ψ (p, 0)⟫_ℝ) q :
          TangentSpace (𝓡 2) q →L[ℝ] ℝ) = 0 ↔ q = D.point
      exact neg_eq_zero.trans (D.unique_critical q hq)
    morse := D.morse
    morse_smooth := D.morse_smooth
    morse_inverse := D.morse_inverse
    morse_point := D.morse_point
    morseSign1 := -D.morseSign1
    morseSign2 := -D.morseSign2
    morseSign1_sq := by simpa only [neg_mul_neg] using D.morseSign1_sq
    morseSigns_opposite := congrArg Neg.neg D.morseSigns_opposite
    morse_height := by
      intro q hq
      simp only [coe_neg_sphere, inner_neg_left]
      have h := D.morse_height q hq
      linarith
    protectedSet := D.protectedSet
    protected_open := D.protected_open
    point_mem_protected := D.point_mem_protected
    protected_closure := D.protected_closure
    cutRadius := D.cutRadius
    removal_lt_cutRadius := D.removal_lt_cutRadius
    cutRadius_lt_gap := by
      intro i
      change D.cutRadius i < |-(D.cap i).cutHeight -
        ⟪((-u : UnitTwoSphere) : E3), ψ (D.point, 0)⟫_ℝ|
      simpa only [coe_neg_sphere, inner_neg_left, neg_sub_neg, abs_sub_comm] using
        D.cutRadius_lt_gap i
    cut_side := by
      intro i
      change (-(D.cap i).sign = 1 ∧ -(D.cap i).cutHeight <
        ⟪((-u : UnitTwoSphere) : E3), ψ (D.point, 0)⟫_ℝ) ∨
        (-(D.cap i).sign = -1 ∧ ⟪((-u : UnitTwoSphere) : E3), ψ (D.point, 0)⟫_ℝ <
          -(D.cap i).cutHeight)
      rw [coe_neg_sphere, inner_neg_left]
      rcases D.cut_side i with h | h
      · exact Or.inr ⟨by rw [h.1], neg_lt_neg h.2⟩
      · exact Or.inl ⟨by rw [h.1]; norm_num, neg_lt_neg h.2⟩ }



theorem SaddlePieceData.reverseHeight_geometry (D : SaddlePieceData ψ u) :
    D.reverseHeight.capCount = D.capCount ∧
      D.reverseHeight.sourceCore = D.sourceCore ∧ D.reverseHeight.point = D.point ∧
      D.reverseHeight.morse = D.morse ∧ D.reverseHeight.protectedSet = D.protectedSet ∧
      D.reverseHeight.cutRadius = D.cutRadius ∧
      D.reverseHeight.slabLower = -D.slabUpper ∧ D.reverseHeight.slabUpper = -D.slabLower ∧
      D.reverseHeight.morseSign1 = -D.morseSign1 ∧
      D.reverseHeight.morseSign2 = -D.morseSign2 ∧
      ∀ i : Fin D.capCount, D.reverseHeight.cap i = (D.cap i).reverseHeight :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

end PoincareConjecture.M25.Topology3D
