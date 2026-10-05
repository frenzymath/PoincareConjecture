import PoincareLib.Geometry.RicciFlow.Pullback
import PoincareLib.Geometry.Manifold.InverseFunction.LocalDiffeomorph
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Basic
import PoincareLib.Geometry.Riemannian.Connection.Construction
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryInvariants

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

/-- The smooth open embedding of a selected surgery component is a local
diffeomorphism.  The inverse is only given on the open range, so the right
derivative identity is obtained from the local equality with the identity. -/
noncomputable def selectedComponentInclusionLocalDiffeomorph
    {A : GeneralizedSliceCarrier.{u}}
    (C : SurgerySelectedComponent A) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ C.inclusion := by
  apply Poincare.isLocalDiffeomorph_of_contMDiff_bijective_mfderiv
    C.inclusion_smooth
  intro x
  let f := C.inclusion
  let g := C.inverse
  have hfr : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x := C.inclusion_smooth.contMDiffAt
  have hgr : ContMDiffAt (𝓡 3) (𝓡 3) ∞ g (f x) := by
    apply C.inverse_smooth.contMDiffAt
    exact C.inclusion_openEmbedding.isOpen_range.mem_nhds ⟨x, rfl⟩
  have hcomp := mfderiv_comp x
    (hgr.mdifferentiableAt (by simp))
    (hfr.mdifferentiableAt (by simp))
  have hleft : g ∘ f = id := by
    funext y
    exact C.left_inverse y
  have hcomp' :
      (mfderiv (𝓡 3) (𝓡 3) g (f x)).comp
          (mfderiv (𝓡 3) (𝓡 3) f x) =
        ContinuousLinearMap.id ℝ _ := by
    rw [← hcomp, hleft, mfderiv_id]
  have hinj : Function.Injective
      (mfderiv (𝓡 3) (𝓡 3) f x) := by
    intro v w hvw
    have hv := congrArg (fun L => L v) hcomp'
    have hw := congrArg (fun L => L w) hcomp'
    change (mfderiv (𝓡 3) (𝓡 3) g (f x))
      ((mfderiv (𝓡 3) (𝓡 3) f x) v) = v at hv
    change (mfderiv (𝓡 3) (𝓡 3) g (f x))
      ((mfderiv (𝓡 3) (𝓡 3) f x) w) = w at hw
    exact hv.symm.trans ((congrArg _ hvw).trans hw)
  have hright : ∀ᶠ y in 𝓝 (f x), f (g y) = y := by
    filter_upwards [C.inclusion_openEmbedding.isOpen_range.mem_nhds ⟨x, rfl⟩] with y hy
    obtain ⟨z, rfl⟩ := hy
    exact congrArg f (C.left_inverse z)
  have hcomp2 := mfderiv_comp (f := g) (g := f) (f x)
    (C.left_inverse x ▸ hfr.mdifferentiableAt (by simp))
    (hgr.mdifferentiableAt (by simp))
  have hcomp2' := hcomp2
  rw [show g (f x) = x from C.left_inverse x] at hcomp2'
  have hright_eq : (f ∘ g) =ᶠ[𝓝 (f x)] id := by
    filter_upwards [hright] with y hy
    exact hy
  have hcomp2'' :
      (mfderiv (𝓡 3) (𝓡 3) f x).comp
          (mfderiv (𝓡 3) (𝓡 3) g (f x)) =
        ContinuousLinearMap.id ℝ _ := by
    rw [← hcomp2', hright_eq.mfderiv_eq, mfderiv_id]
  have hsurj : Function.Surjective
      (mfderiv (𝓡 3) (𝓡 3) f x) := by
    intro y
    refine ⟨(mfderiv (𝓡 3) (𝓡 3) g (f x)) y, ?_⟩
    exact congrArg (fun L => L y) hcomp2''
  exact ⟨by simpa [f] using hinj, by simpa [f] using hsurj⟩

/-- Pull back an ambient Ricci flow to the fixed carrier of a selected
component. -/
noncomputable def selectedComponentRicciFlow
    {A : GeneralizedSliceCarrier.{u}}
    {J : Set ℝ}
    (C : SurgerySelectedComponent A)
    (F : RicciFlow 3 A.carrier J) :
    RicciFlow 3 C.carrier.carrier J :=
  F.pullbackWithConnection C.inclusion
    (selectedComponentInclusionLocalDiffeomorph C)
    (fun t => RiemannianMetric.leviCivitaData
      ((F.metric t).pullbackOfLocalDiffeomorph C.inclusion
        (selectedComponentInclusionLocalDiffeomorph C)))

@[simp] theorem selectedComponentRicciFlow_metric
    {A : GeneralizedSliceCarrier.{u}}
    {J : Set ℝ}
    (C : SurgerySelectedComponent A)
    (F : RicciFlow 3 A.carrier J) (t : ℝ) (x : C.carrier.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    ((selectedComponentRicciFlow C F).metric t).inner x v w =
      (F.metric t).inner (C.inclusion x)
        (mfderiv (𝓡 3) (𝓡 3) C.inclusion x v)
        (mfderiv (𝓡 3) (𝓡 3) C.inclusion x w) := rfl

@[simp] theorem selectedComponentRicciFlow_scalarCurvature
    {A : GeneralizedSliceCarrier.{u}}
    {J : Set ℝ}
    (C : SurgerySelectedComponent A)
    (F : RicciFlow 3 A.carrier J) (t : ℝ) (x : C.carrier.carrier) :
    ((selectedComponentRicciFlow C F).connection t).scalarCurvature x =
      (F.connection t).scalarCurvature (C.inclusion x) := by
  apply ((selectedComponentRicciFlow C F).connection t).scalarCurvature_eq_of_local_isometry
    (F.connection t) isOpen_univ C.inclusion_smooth.contMDiffOn
    (fun _ _ _ _ => rfl) (Set.mem_univ x)

end PoincareMT
