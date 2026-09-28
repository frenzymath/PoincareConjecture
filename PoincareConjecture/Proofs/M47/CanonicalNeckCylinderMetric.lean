import PoincareConjecture.Proofs.M47.SeedCylinderSource









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47

variable {F : SurgeryFlowData.{u}} {C B : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}



theorem neck_reclock_pullbackInner
    (e : SurgeryFlowCylinder F C origin scale I U)
    {nextOrigin nextScale : ℝ} {J : Set ℝ}
    (hscale : 0 < nextScale) (hJ : J.OrdConnected) (phi : ℝ → ℝ)
    (hmem : MapsTo phi J I) (hmono : StrictMonoOn phi J)
    (hclock : ∀ s ∈ J, nextOrigin + s / nextScale = origin + phi s / scale)
    (s : ℝ) (hs : s ∈ J) (x : C.carrier) (v w : TangentSpace (𝓡 3) x) :
    (seedCylinderReclock e hscale hJ phi hmem hmono hclock).pullbackInner s hs x v w =
      (nextScale / scale) * e.pullbackInner (phi s) (hmem hs) x v w := by
  have hfunctions :
      (⟨nextOrigin + s / nextScale,
        (seedCylinderReclock e hscale hJ phi hmem hmono hclock).forward s hs⟩ :
          (t : ℝ) × (C.carrier → (F.slice t).carrier)) =
        ⟨origin + phi s / scale, e.forward (phi s) (hmem hs)⟩ := by
    apply Sigma.ext (hclock s hs)
    apply Function.hfunext rfl
    intro y y' hyy
    cases hyy
    exact seedCylinderReclock_forward_heq e hscale hJ phi hmem hmono hclock s hs y
  have hm := congrArg (fun p : (t : ℝ) × (C.carrier → (F.slice t).carrier) =>
    (F.metric p.1).inner (p.2 x)
      (mfderiv (𝓡 3) (𝓡 3) p.2 x v) (mfderiv (𝓡 3) (𝓡 3) p.2 x w)) hfunctions
  unfold SurgeryFlowCylinder.pullbackInner
  rw [hm]
  field_simp [e.scale_pos.ne']



theorem neck_reclock_cylinderPullback
    (e : SurgeryFlowCylinder F C origin scale I U)
    {nextOrigin nextScale : ℝ} {J : Set ℝ}
    (hscale : 0 < nextScale) (hJ : J.OrdConnected) (phi : ℝ → ℝ)
    (hmem : MapsTo phi J I) (hmono : StrictMonoOn phi J)
    (hclock : ∀ s ∈ J, nextOrigin + s / nextScale = origin + phi s / scale)
    (coordinate : RoundCylinderSpace → C.carrier)
    (s : ℝ) (hs : s ∈ J) (z : RoundCylinderSpace) (v w : RoundCylinderTangent z) :
    surgeryCylinderPullback (seedCylinderReclock e hscale hJ phi hmem hmono hclock)
        coordinate s z v w =
      (nextScale / scale) * surgeryCylinderPullback e coordinate (phi s) z v w := by
  simp only [surgeryCylinderPullback, dif_pos hs, dif_pos (hmem hs)]
  exact neck_reclock_pullbackInner e hscale hJ phi hmem hmono hclock s hs _ _ _



theorem neck_source_pullbackInner
    (e : SurgeryFlowCylinder F C origin scale I U)
    (D : PartialDiffeomorph (𝓡 3) (𝓡 3) B.carrier C.carrier ∞)
    (V : Set B.carrier) (hV : V ⊆ D.source) (hmaps : MapsTo D V U)
    (hU : IsOpen U) (s : ℝ) (hs : s ∈ I) {x : B.carrier} (hx : x ∈ V)
    (v w : TangentSpace (𝓡 3) x) :
    (seedCylinderSource e D V hV hmaps).pullbackInner s hs x v w =
      e.pullbackInner s hs (D x) (mfderiv (𝓡 3) (𝓡 3) D x v)
        (mfderiv (𝓡 3) (𝓡 3) D x w) := by
  have hD := (D.contMDiffOn.contMDiffAt
    (D.open_source.mem_nhds (hV hx))).mdifferentiableAt (by simp)
  have hE := ((e.forward_smooth s hs).contMDiffAt
    (hU.mem_nhds (hmaps hx))).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp x hE hD
  change scale * (F.metric _).inner (e.forward s hs (D x))
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ D) x v)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ D) x w) = _
  rw [hchain]
  rfl



theorem neck_source_inverse_pullbackInner
    (e : SurgeryFlowCylinder F C origin scale I U)
    (D : PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier B.carrier ∞)
    (V : Set B.carrier) (hV : V ⊆ D.target) (hmaps : MapsTo D.symm V U)
    (hU : IsOpen U) (s : ℝ) (hs : s ∈ I) {x : C.carrier}
    (hx : x ∈ D.source) (hxV : D x ∈ V) (v w : TangentSpace (𝓡 3) x) :
    (seedCylinderSource e D.symm V hV hmaps).pullbackInner s hs (D x)
        (mfderiv (𝓡 3) (𝓡 3) D x v) (mfderiv (𝓡 3) (𝓡 3) D x w) =
      e.pullbackInner s hs x v w := by
  have he : D.toOpenPartialHomeomorph.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨D.mdifferentiableOn (by simp), D.symm.mdifferentiableOn (by simp)⟩
  have hd : (mfderiv (𝓡 3) (𝓡 3) D.symm (D x)).comp
      (mfderiv (𝓡 3) (𝓡 3) D x) =
        ContinuousLinearMap.id ℝ (TangentSpace (𝓡 3) x) := he.symm_comp_deriv hx
  have hv : mfderiv (𝓡 3) (𝓡 3) D.symm (D x)
      (mfderiv (𝓡 3) (𝓡 3) D x v) = v := congrArg (fun A => A v) hd
  have hw : mfderiv (𝓡 3) (𝓡 3) D.symm (D x)
      (mfderiv (𝓡 3) (𝓡 3) D x w) = w := congrArg (fun A => A w) hd
  have hm := neck_source_pullbackInner e D.symm V hV hmaps hU s hs hxV
    (mfderiv (𝓡 3) (𝓡 3) D x v) (mfderiv (𝓡 3) (𝓡 3) D x w)
  rw [hv, hw] at hm
  have hleft : D.symm.toPartialEquiv (D.toPartialEquiv x) = x := D.left_inv hx
  exact hm.trans (congrArg (fun y : C.carrier => e.pullbackInner s hs y v w) hleft)

end PoincareConjecture.Proofs.M47
