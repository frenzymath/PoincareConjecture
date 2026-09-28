import PoincareConjecture.Proofs.M47.GeneralizedBridgeCylinder
import PoincareConjecture.Proofs.M47.GeneralizedBridgeNeckGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W) {t : ℝ} (ht : t ∈ H.generalized.interval)

theorem regular_history_terminal_carrier
    {scale a : ℝ} (ha : a < 0) {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t scale (Ioc a 0) U)
    (hbase : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x) :
    U ⊆ range (H.history.forward t ht) := by
  rw [H.regular_range]
  intro x hx
  have hzero : (0 : ℝ) ∈ Ioc a 0 := ⟨ha, le_rfl⟩
  have he : (⟨t + 0 / scale, e.forward 0 hzero x⟩ : Σ s, (F.slice s).carrier) =
      ⟨t, x⟩ := Sigma.ext (by simp) (hbase hzero x hx)
  exact (congrArg (fun p : Σ s, (F.slice s).carrier =>
    p.2 ∈ m33RegularRegion F p.1) he).mp (e.regular_image_Ioc hzero ⟨x, hx, rfl⟩)

theorem exists_regular_history_strong_neck {epsilon : ℝ}
    (N : SurgeryStrongNeck F t epsilon) :
    ∃ N' : GeneralizedStrongNeck H.generalized t epsilon,
      N'.center = H.history.inverse t ht N.neck.center ∧
      N'.scale = N.neck.scale ∧
      N'.carrier = H.history.forward t ht ⁻¹' N.neck.carrier := by
  rcases N with ⟨N, rfl, hconnection, e, hbase, hcomparison⟩
  have hU := regular_history_terminal_carrier H ht (by norm_num : (-1 : ℝ) < 0) e hbase
  let N' := regular_history_static_neck H ht N hconnection hU
  obtain ⟨d, hforward, hpullback⟩ :=
    exists_regular_history_backward_cylinder H ht N.carrier_open e
  let d' := regular_history_rebase_cylinder H ht N.carrier d
  have hmaps : MapsTo N.coordinate_map (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
      (range (H.history.forward t ht)) :=
    fun _ hz => hU (N.coordinatePartialDiffeomorph.map_source hz)
  have hterminal : ∀ h x, x ∈ N'.carrier →
      d'.pointMap 0 h x = (⟨t, x⟩ : H.generalized.point) := by
    intro h x hx
    apply Sigma.ext (by simp [GeneralizedFlowCylinder.pointMap])
    have hphysical := hforward 0 h (H.history.forward t ht x) hx
    have hcancel (s : ℝ) (hst : s = t) (hs : s ∈ H.generalized.interval)
        (y : (H.generalized.slice s).carrier)
        (heq : HEq (H.history.forward s hs y) (H.history.forward t ht x)) : HEq y x := by
      subst s
      exact heq_of_eq ((H.history.forward_openEmbedding t ht).injective
        (eq_of_heq heq))
    exact hcancel (t + 0 / N.scale⁻¹ ^ 2) (by simp)
      (regular_history_backward_cylinder_time H ht e 0 h)
      (d.forward 0 h (H.history.forward t ht x))
      ((heq_of_eq hphysical).trans (hbase h _ hx))
  have hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (generalizedCylinderPullback d' N'.coordinate_map) := by
    apply M35.cylinder_family_congr _ hcomparison
    intro s hs z hz v w
    have hzV : z ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := ⟨mem_univ _, hz⟩
    have hzN : N.coordinate_map z ∈ N.carrier := N.coordinatePartialDiffeomorph.map_source hzV
    have hright : H.history.forward t ht (N'.coordinate_map z) = N.coordinate_map z :=
      H.history.right_inverse t ht (hU hzN)
    have hcoord : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ N'.coordinate_map
        (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) := N'.coordinate_map_smooth
    have hderiv : (mfderiv (𝓡 3) (𝓡 3) (H.history.forward t ht) (N'.coordinate_map z)).comp
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N'.coordinate_map z) =
          mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z := by
      rw [← mfderiv_comp z
        ((H.history.forward_smooth t ht).mdifferentiable (by simp) _)
        (((hcoord.mdifferentiableOn (by simp)) z hzV).mdifferentiableAt
          ((isOpen_univ.prod isOpen_Ioo).mem_nhds hzV))]
      apply Filter.EventuallyEq.mfderiv_eq
      filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds hzV] with q hq
      exact H.history.right_inverse t ht (hmaps hq)
    simp only [surgeryCylinderPullback, generalizedCylinderPullback, dif_pos hs]
    rw [regular_history_rebase_pullback H ht N.carrier d N.carrier_open s hs
      (N'.coordinate_map z) (hright.symm ▸ hzN)]
    simp only [← ContinuousLinearMap.comp_apply, hderiv]
    rw [hright]
    exact (hpullback s hs (N.coordinate_map z) hzN _ _).symm
  refine ⟨{
    epsilon_pos := N'.epsilon_pos
    center := N'.center
    scalar_center_pos := N'.scalar_center_pos
    scale := N'.scale
    scale_pos := N'.scale_pos
    scale_scalar := N'.scale_eq_scalar
    carrier := N'.carrier
    carrier_open := N'.carrier_open
    coordinate := N'.coordinate
    coordinate_map := N'.coordinate_map
    coordinate_map_eq := N'.coordinate_map_eq
    coordinate_map_smooth := N'.coordinate_map_smooth
    coordinate_inverse := N'.coordinate_inverse
    coordinate_inverse_mem := fun x hx => (N'.coordinate_inverse_mem x hx).2
    coordinate_inverse_left := N'.coordinate_inverse_left
    coordinate_inverse_right := ?_
    coordinate_inverse_smooth := N'.coordinate_inverse_smooth
    central_sphere := N'.central_sphere
    central_sphere_eq := N'.central_sphere_eq
    center_on_central_sphere := N'.center_on_central_sphere
    central_sphere_subset := N'.central_sphere_subset
    time_cylinder := d'
    cylinder_identity := hterminal
    metric_comparison := hfamily
  }, rfl, rfl, rfl⟩
  intro x hx
  exact N'.coordinatePartialDiffeomorph.right_inv hx

theorem regular_history_neck_control {epsilon C : ℝ}
    (x : (H.generalized.slice t).carrier) (N : SurgeryStrongNeck F t epsilon)
    (hcenter : N.neck.center = H.history.forward t ht x) :
    Nonempty (GeneralizedCanonicalControl (F := H.generalized) t x epsilon C) := by
  obtain ⟨N', hcenter', _, _⟩ := exists_regular_history_strong_neck H ht N
  refine ⟨GeneralizedCanonicalControl.neck N' ?_⟩
  rw [hcenter', hcenter, H.history.left_inverse t ht x]

end PoincareConjecture.M47
