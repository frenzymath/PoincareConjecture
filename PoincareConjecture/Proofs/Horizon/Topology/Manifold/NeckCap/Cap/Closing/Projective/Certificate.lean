import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Certificate
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.ProjectiveModel










noncomputable section
set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.StandardProjectiveSmoothCover

local notation "E3" => EuclideanSpace ℝ (Fin 3)



theorem nonempty_closedComponentCertificate
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (Y : Opens M) (P : StandardProjectiveSmoothCover Y)
    (hcompact : IsCompact (Y : Set M))
    (hcomponent : ∃ x : M, (Y : Set M) = connectedComponent x) :
    Nonempty (ClosedComponentCertificate .realProjectiveThree (Y : Set M)) := by
  classical
  have hY : Nonempty Y := by
    obtain ⟨x, hx⟩ := hcomponent
    exact ⟨⟨x, hx.symm.subset mem_connectedComponent⟩⟩
  let inv : M → Y := fun x => if hx : x ∈ Y then ⟨x, hx⟩ else Classical.choice hY
  have hinv (x : M) (hx : x ∈ Y) : (inv x : M) = x := by simp [inv, hx]
  have hinv_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inv (Y : Set M) := by
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff Y inv (Y : Set M) x).mp
    apply contMDiffWithinAt_id.congr
    · intro y hy
      exact hinv y hy
    · exact hinv x hx
  let S : SmoothClosedComponentModel .realProjectiveThree (Y : Set M) := {
    model := Y
    model_topology := inferInstance
    model_charted := inferInstance
    model_manifold := inferInstance
    standard_model := P.homeomorph
    standard_smooth := ⟨P⟩
    forward := Subtype.val
    inverse := inv
    forward_mem := fun x => x.property
    left_inverse := hinv
    right_inverse := fun x => Subtype.ext (hinv x x.property)
    forward_smooth := contMDiff_subtype_val
    inverse_smooth := hinv_smooth }
  exact S.nonempty_closedComponentCertificate hcompact hcomponent

end PoincareConjecture.StandardProjectiveSmoothCover
