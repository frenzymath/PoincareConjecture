import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.TensorRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture

theorem GeneralizedRicciFlowData.roundCylinderPullback_of_point_eq
    (F : GeneralizedRicciFlowData.{u}) {a b ε : ℝ} (hab : a = b)
    (f : RoundCylinderSpace → (F.slice a).carrier)
    (g : RoundCylinderSpace → (F.slice b).carrier)
    (heq : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
      (⟨a, f z⟩ : F.point) = ⟨b, g z⟩)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹)
    (v w : RoundCylinderTangent z) :
    roundCylinderPullback (F.metric a) f z v w =
      roundCylinderPullback (F.metric b) g z v w := by
  subst b
  have hlocal : f =ᶠ[𝓝 z] g := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show z ∈ (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ : Set RoundCylinderSpace) from
        ⟨mem_univ _, hz⟩)] with y hy
    exact eq_of_heq (Sigma.mk.inj (heq y hy.2)).2
  simp only [roundCylinderPullback,
    hlocal.mfderiv_eq (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) (I' := 𝓡 3)]
  erw [hlocal.self_of_nhds]

namespace GeneralizedFlowCylinder

variable {F : GeneralizedRicciFlowData.{u}} {C C' : GeneralizedSliceCarrier.{u}}
  {a q b Q ε : ℝ} {I J : Set ℝ} {U : Set C.carrier} {V : Set C'.carrier}

theorem tensor_eq_composite (e : GeneralizedFlowCylinder F C a q I U)
    (hU : IsOpen U) {f : RoundCylinderSpace → C.carrier}
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (hmap : MapsTo f (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) U)
    (s : ℝ) (hs : s ∈ I) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹) (v w : RoundCylinderTangent z) :
    generalizedCylinderPullback e f s z v w =
      q * roundCylinderPullback (F.metric (a + s / q)) (e.forward s hs ∘ f) z v w := by
  have hzf : z ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ := ⟨mem_univ _, hz⟩
  have he := ((e.forward_smooth s hs).contMDiffAt
    (hU.mem_nhds (hmap hzf))).mdifferentiableAt (by simp)
  have hfd := (hf.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hzf)).mdifferentiableAt (by simp)
  simp only [generalizedCylinderPullback, dif_pos hs, pullbackInner,
    roundCylinderPullback, mfderiv_comp z he hfd, ContinuousLinearMap.comp_apply,
    Function.comp_apply]

theorem tensor_eq_of_pointMap_eq
    (e : GeneralizedFlowCylinder F C a q I U)
    (d : GeneralizedFlowCylinder F C' b Q J V)
    (hU : IsOpen U) (hV : IsOpen V)
    {f : RoundCylinderSpace → C.carrier} {g : RoundCylinderSpace → C'.carrier}
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (hg : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ g
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (hfmap : MapsTo f (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) U)
    (hgmap : MapsTo g (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) V)
    {s r : ℝ} (hs : s ∈ I) (hr : r ∈ J) (htime : a + s / q = b + r / Q)
    (hpoint : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
      e.pointMap s hs (f z) = d.pointMap r hr (g z))
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-ε⁻¹) ε⁻¹)
    (v w : RoundCylinderTangent z) :
    generalizedCylinderPullback e f s z v w =
      q / Q * generalizedCylinderPullback d g r z v w := by
  rw [e.tensor_eq_composite hU hf hfmap s hs z hz,
    d.tensor_eq_composite hV hg hgmap r hr z hz,
    F.roundCylinderPullback_of_point_eq htime (e.forward s hs ∘ f)
      (d.forward r hr ∘ g) hpoint z hz]
  field_simp [d.scale_pos.ne']

end GeneralizedFlowCylinder
end PoincareConjecture
