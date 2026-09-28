import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_CenteredInverse
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_RecentNeck
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_Normalization











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M45NeckGluingInput

open M36 M45

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {epsilon beta : ℝ} (I : M45NeckGluingInput.{u} epsilon beta)



noncomputable def recentCenteredMap (z : RoundCylinderSpace) : E → I.recent_carrier.carrier :=
  I.recent_patch.coordinate ∘ centeredCylinderLift z.1 z.2



noncomputable def olderCenteredCoordinate (z : RoundCylinderSpace) : RoundCylinderSpace :=
  I.older_neck.neck.coordinate_inverse (I.identify (I.recent_patch.coordinate z))



noncomputable def olderCenteredMap (z : RoundCylinderSpace) : E → I.older_carrier.carrier :=
  centeredNeckLift I.older_neck.neck
    (I.olderCenteredCoordinate z).1 (I.olderCenteredCoordinate z).2




theorem exists_joining_centered_transition
    (hpos : 0 < beta * epsilon) (hsmall : beta * epsilon < 1 / 2)
    (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-(beta * epsilon)⁻¹) (beta * epsilon)⁻¹) :
    ∃ (phi : E → E) (U : Set E), IsOpen U ∧ (0 : E) ∈ U ∧
      U ⊆ centeredNeckDomain (I.recentNeck hpos hsmall) z.2 ∧
      ContDiffOn ℝ ∞ phi U ∧
      MapsTo phi U (centeredNeckDomain I.older_neck.neck (I.olderCenteredCoordinate z).2) ∧
      phi 0 = 0 ∧ (fderiv ℝ phi 0).IsInvertible ∧
      ∀ p ∈ U, I.olderCenteredMap z (phi p) = I.identify (I.recentCenteredMap z p) := by
  let N := I.recentNeck hpos hsmall
  let O := I.older_neck.neck
  let A := I.recentCenteredMap z
  let F := I.identify ∘ A
  let w := I.olderCenteredCoordinate z
  let K := centeredNeckInverse O w.1 w.2
  let U0 := centeredNeckDomain N z.2
  have hU0 : IsOpen U0 := centeredNeckDomain_isOpen N z.2
  have hzero : (0 : E) ∈ U0 := zero_mem_centeredNeckDomain N hz
  have hA : ContMDiffOn (𝓡 3) (𝓡 3) ∞ A U0 :=
    fun p hp => (centeredNeckLift_contMDiffAt N z.1 z.2 hp).contMDiffWithinAt
  have hAmem (p : E) (hp : p ∈ U0) : A p ∈ I.recent_patch.carrier :=
    centeredNeckLift_mem N z.1 z.2 hp
  have hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ F U0 :=
    I.identify_smooth.comp hA hAmem
  have hFmem (p : E) (hp : p ∈ U0) : F p ∈ O.carrier :=
    I.identify_image (mem_image_of_mem I.identify (hAmem p hp))
  have hA0 : A 0 = I.recent_patch.coordinate z := by
    dsimp only [A, recentCenteredMap]
    rw [Function.comp_apply, centeredCylinderLift_zero]
  have hw : O.coordinate_inverse (F 0) = w := by
    dsimp only [F, Function.comp_apply]
    rw [hA0]
    rfl
  let V := O.carrier ∩ O.coordinate_inverse ⁻¹' ((chartAt E2 w.1).source ×ˢ univ)
  have hV : IsOpen V := O.coordinate_inverse_smooth.continuousOn.isOpen_inter_preimage
    O.carrier_open ((chartAt E2 w.1).open_source.prod isOpen_univ)
  have hFV : F 0 ∈ V := ⟨hFmem 0 hzero, by
    change (O.coordinate_inverse (F 0)).1 ∈ (chartAt E2 w.1).source ∧ _
    rw [hw]
    exact ⟨mem_chart_source E2 w.1, mem_univ _⟩⟩
  let U := U0 ∩ F ⁻¹' V
  have hU : IsOpen U := hF.continuousOn.isOpen_inter_preimage hU0 hV
  have h0U : (0 : E) ∈ U := ⟨hzero, hFV⟩
  have hK (y : I.older_carrier.carrier) (hy : y ∈ V) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ K y := by
    have hm := centeredNeckInverse_mem O w.1 w.2 hy.1
    have hi := centeredNeckInverse_contMDiffAt_lift O w.1 w.2 hm
    rwa [centeredNeckLift_inverse O w.1 w.2 hy.1 hy.2.1] at hi
  have hphi : ContDiffOn ℝ ∞ (K ∘ F) U := by
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    exact ((hK (F p) hp.2).comp p
      (hF.contMDiffAt (hU0.mem_nhds hp.1))).contDiffAt
  have hK0 := centeredNeckInverse_at_center O (hFmem 0 hzero)
  rw [hw] at hK0
  have hFi : (mfderiv (𝓡 3) (𝓡 3) F 0).IsInvertible := by
    rw [mfderiv_comp 0
      ((I.identify_smooth.contMDiffAt (I.recent_patch.carrier_open.mem_nhds
        (hAmem 0 hzero))).mdifferentiableAt (by simp))
      ((hA.contMDiffAt (hU0.mem_nhds hzero)).mdifferentiableAt (by simp))]
    exact (I.identify_mfderiv_invertible (A 0) (hAmem 0 hzero)).comp
      (centeredNeckLift_mfderiv_isInvertible N z.1 z.2 hzero)
  refine ⟨K ∘ F, U, hU, h0U, inter_subset_left, hphi, ?_, hK0.1, ?_, ?_⟩
  · intro p hp
    exact centeredNeckInverse_mem O w.1 w.2 hp.2.1
  · rw [← mfderiv_eq_fderiv, mfderiv_comp 0
      (hK0.2.1.mdifferentiableAt (by simp))
      ((hF.contMDiffAt (hU0.mem_nhds hzero)).mdifferentiableAt (by simp))]
    exact hK0.2.2.comp hFi
  · intro p hp
    exact centeredNeckLift_inverse O w.1 w.2 hp.2.1 hp.2.2.1

end PoincareConjecture.M45NeckGluingInput
