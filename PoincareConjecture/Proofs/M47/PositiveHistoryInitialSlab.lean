import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Restriction
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47Positive

theorem exists_component_slab_pullback
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} (U : TopologicalSpace.Opens C.carrier)
    (e : SurgeryFlowCylinder F C origin scale I U)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ F.time_domain)
    (hfree : Disjoint F.surgery_times (Ioc a b))
    (r : ℝ) (hr : r ∈ I) (hr' : origin + r / scale ∈ Icc a b) :
    ∃ G : RicciFlow 3 U (Icc a b),
      ∀ (s : ℝ) (hs : s ∈ I) (_hs' : origin + s / scale ∈ Icc a b)
        (x : U) (v w : TangentSpace (𝓡 3) x),
        (F.metric (origin + s / scale)).inner (e.forward s hs x.val)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) x v)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) x w) =
            (G.metric (origin + s / scale)).inner x v w := by
  let S := F.regular_slabs a b hab hJ hfree
  let phi : U → (F.slice a).carrier :=
    (S.identify ⟨origin + r / scale, hr'⟩).symm ∘ e.forward r hr ∘ Subtype.val
  have hphi : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ phi := by
    intro x
    let d := (M44.cylinderSliceChart e U.isOpen r hr).trans
      (S.identify ⟨origin + r / scale, hr'⟩).symm.toPartialDiffeomorph
    exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U x).comp
      (𝓡 3) (F.slice a).carrier
      (d.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ ⟨x.property, mem_univ _⟩)
  let G := S.flow.pullbackWithConnection phi hphi
    (fun t => ((S.flow.metric t).pullbackOfLocalDiffeomorph phi hphi).leviCivitaData)
  refine ⟨G, ?_⟩
  intro s hs hs' x v w
  have heq : (fun y : U => e.forward s hs y.val) =
      (S.identify ⟨origin + s / scale, hs'⟩) ∘ phi := by
    funext y
    exact (e.slab_compatibility a b hab hJ hfree r hr s hs hr' hs'
      y.val y.property).symm
  change (F.metric (origin + s / scale)).inner
      ((fun y : U => e.forward s hs y.val) x)
      (mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) x v)
      (mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) x w) =
    (S.flow.metric (origin + s / scale)).inner (phi x)
      (mfderiv (𝓡 3) (𝓡 3) phi x v) (mfderiv (𝓡 3) (𝓡 3) phi x w)
  rw [heq, mfderiv_comp x
    ((S.identify ⟨origin + s / scale, hs'⟩).contMDiff.mdifferentiable (by simp) (phi x))
    (hphi.contMDiff.mdifferentiable (by simp) x)]
  exact S.metric_pullback ⟨origin + s / scale, hs'⟩ (phi x) _ _

end PoincareConjecture.M47Positive
