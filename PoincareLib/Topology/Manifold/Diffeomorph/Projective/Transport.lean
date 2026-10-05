import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Models
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import PoincareLib.Geometry.Manifold.OpenEmbedding
import PoincareLib.Geometry.Manifold.LocalDiffeomorph

/-! # Transporting punctured projective covers through smooth coordinates -/

noncomputable section
set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u v

namespace PoincareMT.StandardPuncturedProjectiveCover

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} {N : Type v} [TopologicalSpace M] [ChartedSpace E3 M]
  [TopologicalSpace N] [ChartedSpace E3 N]
  {p : RealProjectiveThree} {A : Set M}

/-- Smooth ambient coordinates transport the actual carrier of a punctured
projective cover, preserving the puncture and its exact antipodal fibers. -/
def transport (S : StandardPuncturedProjectiveCover M p A)
    (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) :
    StandardPuncturedProjectiveCover N p (e '' A) where
  cover := e ∘ S.cover
  image_eq := by rw [image_comp, S.image_eq]
  fibers := fun x y hx hy => e.injective.eq_iff.trans (S.fibers x y hx hy)
  local_diffeomorph := fun x =>
    (S.local_diffeomorph x).comp (𝓡 3) N (e.isLocalDiffeomorph (S.cover x))

@[simp] theorem transport_cover (S : StandardPuncturedProjectiveCover M p A)
    (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (x : UnitThreeSphere) :
    (S.transport e).cover x = e (S.cover x) := rfl

private theorem open_inclusion_inverse_smooth
    (Y : Opens M) [Nonempty Y] :
    ContMDiffOn (M' := Y) (𝓡 3) (𝓡 3) ∞
      (fun x : M => ((Y.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph :
        OpenPartialHomeomorph Y M).symm x : Y)) (Y : Set M) := by
  let i : OpenPartialHomeomorph Y M := Y.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  intro x hx
  apply (ContMDiffWithinAt.subtypeVal_comp_iff Y i.symm (Y : Set M) x).mp
  apply contMDiffWithinAt_id.congr
  · intro y hy
    exact i.right_inv (by simpa [i] using hy)
  · exact i.right_inv (by simpa [i] using hx)

/-- Restrict the codomain to an actual open ambient carrier, retaining its
inherited smooth structure and the exact punctured antipodal fibers. -/
def inOpen (S : StandardPuncturedProjectiveCover M p A)
    (Y : Opens M) [Nonempty Y] (hAY : A ⊆ Y) :
    StandardPuncturedProjectiveCover Y p (Subtype.val ⁻¹' A) := by
  let i : OpenPartialHomeomorph Y M := Y.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  have hit : i.target = (Y : Set M) := by simp [i]
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ i.symm i.target := by
    rw [hit]
    exact open_inclusion_inverse_smooth Y
  have hmem (x : UnitThreeSphere) (hx : Quotient.mk' x ≠ p) : S.cover x ∈ i.target :=
    hit.symm ▸ hAY (S.image_eq.subset (mem_image_of_mem S.cover hx))
  have hval (x : UnitThreeSphere) (hx : Quotient.mk' x ≠ p) :
      (i.symm (S.cover x) : M) = S.cover x := i.right_inv (hmem x hx)
  let I : PartialDiffeomorph (𝓡 3) (𝓡 3) M Y ∞ := {
    toPartialEquiv := i.symm.toPartialEquiv
    open_source := i.open_target
    open_target := i.open_source
    contMDiffOn_toFun := hi
    contMDiffOn_invFun := contMDiff_subtype_val.contMDiffOn }
  refine {
    cover := i.symm ∘ S.cover
    image_eq := ?_
    fibers := ?_
    local_diffeomorph := fun x =>
      (S.local_diffeomorph x).comp (𝓡 3) Y
        ⟨I, hmem x x.property, fun _ _ => rfl⟩ }
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (i.symm (S.cover x) : M) ∈ A
      rw [hval x hx]
      exact S.image_eq.subset (mem_image_of_mem S.cover hx)
    · intro hy
      obtain ⟨x, hx, hxy⟩ := S.image_eq.symm.subset hy
      refine ⟨x, hx, Subtype.ext ?_⟩
      exact (hval x hx).trans hxy
  · intro x y hx hy
    change i.symm (S.cover x) = i.symm (S.cover y) ↔ _
    rw [Subtype.ext_iff, hval x hx, hval y hy]
    exact S.fibers x y hx hy

end PoincareMT.StandardPuncturedProjectiveCover
