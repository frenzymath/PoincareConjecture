import PoincareConjecture.Proofs.M47.GeneralizedBridgeGeometry










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W) {t : ℝ} (ht : t ∈ H.generalized.interval)



noncomputable def regular_history_preimage_homeomorph
    (U : Set (F.slice t).carrier) (hU : U ⊆ range (H.history.forward t ht)) :
    (H.history.forward t ht ⁻¹' U) ≃ₜ U := by
  classical
  exact {
  toFun x := ⟨H.history.forward t ht x.val, x.property⟩
  invFun y := ⟨H.history.inverse t ht y.val, by
    change H.history.forward t ht (H.history.inverse t ht y.val) ∈ U
    rw [H.history.right_inverse t ht (hU y.property)]
    exact y.property⟩
  left_inv x := Subtype.ext (H.history.left_inverse t ht x.val)
  right_inv y := Subtype.ext (H.history.right_inverse t ht (hU y.property))
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (H.history.forward_smooth t ht).continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (H.history.inverse_smooth t ht).continuousOn.comp_continuous
      continuous_subtype_val (fun y : U => hU y.property)
  }



theorem regular_history_coordinate_pullback
    {V : Set RoundCylinderSpace} (hV : IsOpen V)
    (c : RoundCylinderSpace → (F.slice t).carrier)
    (hc : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ c V)
    (himage : MapsTo c V (range (H.history.forward t ht)))
    (z : RoundCylinderSpace) (hz : z ∈ V)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
    roundCylinderPullback (H.generalized.metric t) (H.history.inverse t ht ∘ c) z v w =
      roundCylinderPullback (F.metric t) c z v w := by
  let k := H.history.inverse t ht ∘ c
  have hk : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ k V :=
    (H.history.inverse_smooth t ht).comp hc himage
  have hfk : (H.history.forward t ht ∘ k) =ᶠ[𝓝 z] c := by
    filter_upwards [hV.mem_nhds hz] with q hq
    exact H.history.right_inverse t ht (himage hq)
  have hf := (H.history.forward_smooth t ht).mdifferentiable (by simp) (k z)
  have hkd := ((hk.mdifferentiableOn (by simp)) z hz).mdifferentiableAt (hV.mem_nhds hz)
  have hderiv : (mfderiv (𝓡 3) (𝓡 3) (H.history.forward t ht) (k z)).comp
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) k z) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) c z := by
    rw [← mfderiv_comp z hf hkd]
    exact hfk.mfderiv_eq
  unfold roundCylinderPullback
  change (H.generalized.metric t).inner (k z) _ _ = _
  rw [← H.history.metric_pullback t ht (k z)]
  change (F.metric t).inner (H.history.forward t ht (k z))
    (((mfderiv (𝓡 3) (𝓡 3) (H.history.forward t ht) (k z)).comp
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) k z)) v)
    (((mfderiv (𝓡 3) (𝓡 3) (H.history.forward t ht) (k z)).comp
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) k z)) w) = _
  rw [hderiv]
  have hpoint : H.history.forward t ht (k z) = c z := hfk.eq_of_nhds
  rw [hpoint]

end PoincareConjecture.M47
