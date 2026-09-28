import PoincareConjecture.Proofs.M47.CanonicalNeckCylinderMetric
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
  (e : SurgeryFlowCylinder F C origin scale I U)
  (hU : IsOpen U) (hzero : 0 ∈ I) (V : Set C.carrier) (hVU : V ⊆ U)

noncomputable def neckPushedCylinder :
    SurgeryFlowCylinder F (F.slice (origin + 0 / scale)) (origin + 0 / scale)
      scale I (e.forward 0 hzero '' V) := by
  let chart := M44.cylinderSliceChart e hU 0 hzero
  have hclock : ∀ s ∈ I, (origin + 0 / scale) + s / scale = origin + id s / scale := by
    intro s _hs
    simp only [zero_div, add_zero, id_eq]
  let shifted := seedCylinderReclock e e.scale_pos e.interval_connected id
    (fun _ hs => hs) (fun _ _ _ _ hst => hst) hclock
  have hsource : e.forward 0 hzero '' V ⊆ chart.target := image_mono hVU
  have hmaps : MapsTo chart.symm (e.forward 0 hzero '' V) U :=
    fun _ hx => chart.map_target (hsource hx)
  exact seedCylinderSource shifted chart.symm (e.forward 0 hzero '' V) hsource hmaps

theorem neckPushedCylinder_zero_identity (h : 0 ∈ I)
    (x : (F.slice (origin + 0 / scale)).carrier) (hx : x ∈ e.forward 0 hzero '' V) :
    HEq ((neckPushedCylinder e hU hzero V hVU).forward 0 h x) x := by
  let chart := M44.cylinderSliceChart e hU 0 hzero
  have hclock : ∀ s ∈ I, (origin + 0 / scale) + s / scale = origin + id s / scale := by
    intro s _hs
    simp only [zero_div, add_zero, id_eq]
  have he := seedCylinderReclock_forward_heq e e.scale_pos e.interval_connected id
    (fun _ hs => hs) (fun _ _ _ _ hst => hst) hclock 0 h (chart.symm x)
  change HEq ((neckPushedCylinder e hU hzero V hVU).forward 0 h x)
    (e.forward 0 h (chart.symm x)) at he
  exact he.trans (heq_of_eq (chart.right_inv ((image_mono hVU) hx)))

theorem neckPushedCylinder_pullbackInner
    (s : ℝ) (hs : s ∈ I) {x : C.carrier} (hx : x ∈ V)
    (v w : TangentSpace (𝓡 3) x) :
    (neckPushedCylinder e hU hzero V hVU).pullbackInner s hs (e.forward 0 hzero x)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward 0 hzero) x v)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward 0 hzero) x w) =
      e.pullbackInner s hs x v w := by
  let chart := M44.cylinderSliceChart e hU 0 hzero
  have hclock : ∀ s ∈ I, (origin + 0 / scale) + s / scale = origin + id s / scale := by
    intro s _hs
    simp only [zero_div, add_zero, id_eq]
  let shifted := seedCylinderReclock e e.scale_pos e.interval_connected id
    (fun _ hs => hs) (fun _ _ _ _ hst => hst) hclock
  have hsource : e.forward 0 hzero '' V ⊆ chart.target := image_mono hVU
  have hmaps : MapsTo chart.symm (e.forward 0 hzero '' V) U :=
    fun _ hy => chart.map_target (hsource hy)
  have h := neck_source_inverse_pullbackInner shifted chart (e.forward 0 hzero '' V)
    hsource hmaps hU s hs (hVU hx) (mem_image_of_mem _ hx) v w
  have hc := neck_reclock_pullbackInner e e.scale_pos e.interval_connected id
    (fun _ ht => ht) (fun _ _ _ _ hst => hst) hclock s hs x v w
  rw [div_self e.scale_pos.ne', one_mul] at hc
  exact h.trans hc

theorem neckPushedCylinder_cylinderPullback
    (s : ℝ) (hs : s ∈ I) {coordinate : RoundCylinderSpace → C.carrier}
    {z : RoundCylinderSpace}
    (hcoordinate : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z)
    (hz : coordinate z ∈ V) (v w : RoundCylinderTangent z) :
    surgeryCylinderPullback (neckPushedCylinder e hU hzero V hVU)
        (e.forward 0 hzero ∘ coordinate) s z v w =
      surgeryCylinderPullback e coordinate s z v w := by
  have he := ((e.forward_smooth 0 hzero).contMDiffAt
    (hU.mem_nhds (hVU hz))).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp z he hcoordinate
  simp only [surgeryCylinderPullback, dif_pos hs, Function.comp_apply,
    hchain, ContinuousLinearMap.comp_apply]
  exact neckPushedCylinder_pullbackInner e hU hzero V hVU s hs hz _ _

end PoincareConjecture.Proofs.M47
