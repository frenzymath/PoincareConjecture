import PoincareLib.Topology.Manifold.NeckCap.Models
import PoincareLib.Topology.Manifold.Surgery.Event.Sphere.SphereBundles

/-!
# Actual component diffeomorphisms and bundle transport

Whole-slice diffeomorphisms restrict to the inherited component carriers.
The existing bundle transport also applies to the exact geometric bundle
record used by the local surgery conclusion.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M38

/-- Restrict a whole-slice diffeomorphism to the literal connected
components of a point and its image, using their inherited atlases. -/
noncomputable def componentDiffeomorph {A B : GeneralizedSliceCarrier.{u}}
    (e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞) (x : A.carrier) :
    Diffeomorph (𝓡 3) (𝓡 3) (componentCarrier A x).carrier
      (componentCarrier B (e x)).carrier ∞ := by
  let forward : (componentCarrier A x).carrier → (componentCarrier B (e x)).carrier :=
    fun y => ⟨e y.1, e.continuous.image_connectedComponent_subset x
      (Set.mem_image_of_mem e y.property)⟩
  let inverse : (componentCarrier B (e x)).carrier → (componentCarrier A x).carrier :=
    fun y => ⟨e.symm y.1, by
      have hy := e.symm.continuous.image_connectedComponent_subset (e x)
        (Set.mem_image_of_mem e.symm y.property)
      change e.symm y.1 ∈ connectedComponent x
      simpa only [Diffeomorph.symm_apply_apply] using hy⟩
  refine {
    toEquiv := {
      toFun := forward
      invFun := inverse
      left_inv := fun y => Subtype.ext (e.symm_apply_apply y.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1) }
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff (componentOpen B (e x)) forward).mp
    exact e.contMDiff.comp (contMDiff_subtype_val (U := componentOpen A x))
  · apply (ContMDiff.subtypeVal_comp_iff (componentOpen A x) inverse).mp
    exact e.symm.contMDiff.comp (contMDiff_subtype_val (U := componentOpen B (e x)))

/-- Transport an actual surgery sphere-bundle structure by the same
diffeomorphism, retaining its projection and all local trivializations. -/
noncomputable def surgeryBundleAlongDiffeomorph {A B : GeneralizedSliceCarrier.{u}}
    (P : SurgerySphereBundle B)
    (e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞) : SurgerySphereBundle A := by
  let Q : SphereBundleCircleModel.{u} := {
    carrier := B.carrier
    carrier_topology := inferInstance
    carrier_charted := inferInstance
    carrier_manifold := inferInstance
    projection := P.projection
    projection_continuous := P.projection_continuous
    projection_surjective := P.projection_surjective
    projection_smooth := P.projection_smooth
    local_trivialization := P.local_trivialization }
  exact bundleAlongDiffeomorph Q e

end PoincareMT.M38
