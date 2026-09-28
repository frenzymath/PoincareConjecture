import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Flow.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SurgeryRegionEquivalence

variable {A B : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} {V : Set B.carrier}

def symm (e : SurgeryRegionEquivalence A B U V) : SurgeryRegionEquivalence B A V U where
  map := e.inverse
  inverse := e.map
  map_image := e.inverse_image
  inverse_image := e.map_image
  left_inverse := e.right_inverse
  right_inverse := e.left_inverse
  map_smooth := e.inverse_smooth
  inverse_smooth := e.map_smooth

variable (e : SurgeryRegionEquivalence A B U V)

theorem mapsTo : MapsTo e.map U V := by
  intro x hx
  exact e.map_image.subset (mem_image_of_mem _ hx)

theorem mfderiv_bijective {x : A.carrier} (hx : x ∈ interior U) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) e.map x) := by
  have hf := ((e.map_smooth x (interior_subset hx)).contMDiffAt
    (mem_interior_iff_mem_nhds.mp hx)).mdifferentiableAt (by simp)
  have hg := (e.inverse_smooth _ (e.mapsTo (interior_subset hx))).mdifferentiableWithinAt
    (by simp)
  have hc := (hg.hasMFDerivWithinAt.comp x
    (hf.hasMFDerivAt.hasMFDerivWithinAt (s := interior U))
    (e.mapsTo.mono_left interior_subset)).hasMFDerivAt (isOpen_interior.mem_nhds hx)
  have heq : e.inverse ∘ e.map =ᶠ[𝓝 x] id := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact e.left_inverse (interior_subset hy)
  have hd := hc.mfderiv
  rw [heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3), mfderiv_id] at hd
  have hinj : Function.Injective (mfderiv (𝓡 3) (𝓡 3) e.map x) := by
    intro v w hvw
    have hv := congrArg (fun L => L v) hd
    have hw := congrArg (fun L => L w) hd
    simp only [ContinuousLinearMap.comp_apply] at hv hw
    exact hv.trans ((congrArg _ hvw).trans hw.symm)
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : A.carrier → Type _) x
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (mfderiv (𝓡 3) (𝓡 3) e.map x).toLinearMap) rfl).mp hinj⟩

theorem image_isOpen {S : Set A.carrier} (hS : IsOpen S) (hSU : S ⊆ interior U) :
    IsOpen (e.map '' S) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x, hx, rfl⟩
  have hs := (e.map_smooth x (interior_subset (hSU hx))).contMDiffAt
    (mem_interior_iff_mem_nhds.mp (hSU hx))
  rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective hs
    (e.mfderiv_bijective (hSU hx))]
  exact Filter.image_mem_map (hS.mem_nhds hx)

theorem mapsTo_interior : MapsTo e.map (interior U) (interior V) := by
  have hsub : e.map '' interior U ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.mapsTo (interior_subset hx)
  have h := interior_maximal hsub (e.image_isOpen isOpen_interior subset_rfl)
  intro x hx
  exact h (mem_image_of_mem _ hx)

theorem image_interior : e.map '' interior U = interior V := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact e.mapsTo_interior hx
  · intro y hy
    exact ⟨e.inverse y, e.symm.mapsTo_interior hy,
      e.right_inverse (interior_subset hy)⟩

def sourceInterior : TopologicalSpace.Opens A.carrier := ⟨interior U, isOpen_interior⟩

def targetInterior : TopologicalSpace.Opens B.carrier := ⟨interior V, isOpen_interior⟩

noncomputable def interiorDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3) (sourceInterior (U := U)) (targetInterior (V := V)) ∞ where
  toFun x := ⟨e.map x, e.mapsTo_interior x.property⟩
  invFun y := ⟨e.inverse y, e.symm.mapsTo_interior y.property⟩
  left_inv x := Subtype.ext (e.left_inverse (interior_subset x.property))
  right_inv y := Subtype.ext (e.right_inverse (interior_subset y.property))
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (targetInterior (V := V)) _).mp
    intro x
    apply contMDiffAt_subtype_iff.mpr
    exact (e.map_smooth x (interior_subset x.property)).contMDiffAt
      (mem_interior_iff_mem_nhds.mp x.property)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (sourceInterior (U := U)) _).mp
    intro y
    apply contMDiffAt_subtype_iff.mpr
    exact (e.inverse_smooth y (interior_subset y.property)).contMDiffAt
      (mem_interior_iff_mem_nhds.mp y.property)

@[simp] theorem interiorDiffeomorph_apply (x : sourceInterior (U := U)) :
    (e.interiorDiffeomorph x).val = e.map x := rfl

@[simp] theorem interiorDiffeomorph_symm_apply (y : targetInterior (V := V)) :
    (e.interiorDiffeomorph.symm y).val = e.inverse y := rfl

end PoincareConjecture.SurgeryRegionEquivalence
