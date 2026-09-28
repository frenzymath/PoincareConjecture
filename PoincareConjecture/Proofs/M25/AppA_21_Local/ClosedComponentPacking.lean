import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.ClosedComponentCertificate

theorem nonempty_of_compact_connected_opens
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (kind : ClosedComponentKind) (U : TopologicalSpace.Opens M)
    (hcompact : IsCompact (U : Set M))
    (hconnected : IsConnected (U : Set M))
    (standard_model :
      match kind with
      | .threeSphere => U ≃ₜ UnitThreeSphere
      | .realProjectiveThree => U ≃ₜ RealProjectiveThree
      | .realProjectiveThreeConnectedSum =>
          RealProjectiveThreeConnectedSumModel U
            (inferInstance : TopologicalSpace U))
    (standard_smooth :
      match kind with
      | .threeSphere =>
          Nonempty (Diffeomorph (𝓡 3) (𝓡 3) U UnitThreeSphere ∞)
      | .realProjectiveThree =>
          Nonempty (StandardProjectiveSmoothCover U)
      | .realProjectiveThreeConnectedSum =>
          Nonempty (SmoothProjectiveDoubleModel U)) :
    Nonempty (ClosedComponentCertificate kind (U : Set M)) := by
  classical
  obtain ⟨x₀, hx₀⟩ := hconnected.nonempty
  let p : U := ⟨x₀, hx₀⟩
  let r : M → U := fun x => if hx : x ∈ (U : Set M) then ⟨x, hx⟩ else p
  have hleft (x : M) (hx : x ∈ (U : Set M)) : (r x).val = x := by
    simp only [r, dif_pos hx]
  have hright (y : U) : r y.val = y := Subtype.ext (hleft y.val y.property)
  let : CompactSpace U := isCompact_iff_compactSpace.mp hcompact
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp hconnected
  have hclopen : IsClopen (U : Set M) := ⟨hcompact.isClosed, U.isOpen⟩
  have hcomponent : (U : Set M) = connectedComponent x₀ :=
    Subset.antisymm (hconnected.isPreconnected.subset_connectedComponent hx₀)
      (hclopen.connectedComponent_subset hx₀)
  have hrsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ r (U : Set M) := by
    have hc : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Subtype.val ∘ r) (U : Set M) :=
      contMDiff_id.contMDiffOn.congr (fun x hx => hleft x hx)
    intro x hx
    exact (ContMDiffWithinAt.subtypeVal_comp_iff U r (U : Set M) x).mp (hc x hx)
  let topModel : ClosedComponentModel.{u} kind :=
    { carrier := U
      carrier_topology := inferInstance
      compact := inferInstance
      connected := isConnected_univ
      standard_model := standard_model }
  let smoothModel : SmoothClosedComponentModel kind (U : Set M) :=
    { model := U
      model_topology := inferInstance
      model_charted := inferInstance
      model_manifold := inferInstance
      standard_model := standard_model
      standard_smooth := by cases kind <;> exact standard_smooth
      forward := Subtype.val
      inverse := r
      forward_mem := fun y => y.property
      left_inverse := hleft
      right_inverse := hright
      forward_smooth := contMDiff_subtype_val
      inverse_smooth := hrsmooth }
  exact ⟨{
    model := topModel
    homeomorph := Homeomorph.refl U
    connected := hconnected
    compact := hcompact
    component := ⟨x₀, hcomponent⟩
    smooth_model := smoothModel
    model_transport := ⟨Homeomorph.refl U, fun x => (hright x).symm⟩ }⟩

end PoincareConjecture.ClosedComponentCertificate
