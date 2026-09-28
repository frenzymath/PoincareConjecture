import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Models
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.OpenEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph










noncomputable section
set_option autoImplicit false

open Set TopologicalSpace Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.ClosedModels

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]

private def transportMap {U W : Opens M}
    (D : Diffeomorph (𝓡 3) (𝓡 3) U W ∞) (x : M) : M := by
  classical
  exact if hx : x ∈ U then (D ⟨x, hx⟩ : M) else x

private theorem transportMap_apply {U W : Opens M}
    (D : Diffeomorph (𝓡 3) (𝓡 3) U W ∞) (x : U) :
    transportMap D x = (D x : M) := by
  classical
  exact dif_pos x.property

private theorem transportMap_local {U W : Opens M}
    (D : Diffeomorph (𝓡 3) (𝓡 3) U W ∞) :
    IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (transportMap D) (U : Set M) := by
  intro x
  let y : U := ⟨x, x.property⟩
  have hcomp : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (fun z : U => (D z : M)) y :=
    (D.isLocalDiffeomorph y).comp (𝓡 3) M
      (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) W (D y))
  have hlocal : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      ((transportMap D) ∘ (Subtype.val : U → M)) y :=
    hcomp.congr_of_eventuallyEq (Eventually.of_forall (transportMap_apply D))
  exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) U y).of_comp hlocal

private def ambientPartialDiffeomorph (U W : Opens M)
    (D : Diffeomorph (𝓡 3) (𝓡 3) U W ∞) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) M M ∞ where
  toFun := transportMap D
  invFun := transportMap D.symm
  source := U
  target := W
  map_source' := by
    intro x hx
    rw [transportMap_apply D (⟨x, hx⟩ : U)]
    exact (D ⟨x, hx⟩).property
  map_target' := by
    intro x hx
    rw [transportMap_apply D.symm (⟨x, hx⟩ : W)]
    exact (D.symm ⟨x, hx⟩).property
  left_inv' := by
    intro x hx
    rw [transportMap_apply D (⟨x, hx⟩ : U), transportMap_apply D.symm (D ⟨x, hx⟩),
      D.symm_apply_apply]
  right_inv' := by
    intro x hx
    rw [transportMap_apply D.symm (⟨x, hx⟩ : W), transportMap_apply D (D.symm ⟨x, hx⟩),
      D.apply_symm_apply]
  open_source := U.isOpen
  open_target := W.isOpen
  contMDiffOn_toFun := (transportMap_local D).contMDiffOn
  contMDiffOn_invFun := (transportMap_local D.symm).contMDiffOn



theorem exists_euclidean_chart_of_open_diffeomorph
    (U W : Opens M) (D : Diffeomorph (𝓡 3) (𝓡 3) U W ∞)
    (e : OpenPartialHomeomorph M E3) (hes : e.source = (U : Set M))
    (het : e.target = univ)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) :
    ∃ f : OpenPartialHomeomorph M E3,
      f.source = (W : Set M) ∧ f.target = univ ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ f f.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ f.symm f.target := by
  let d := (ambientPartialDiffeomorph U W D).toOpenPartialHomeomorph
  let f := d.symm.trans e
  have hfs : f.source = (W : Set M) := by
    apply inter_eq_left.mpr
    intro x hx
    exact hes.symm.subset (d.map_target hx)
  have hft : f.target = univ := by
    change e.target ∩ e.symm ⁻¹' d.source = univ
    have hsub : e.target ⊆ e.symm ⁻¹' d.source := by
      intro x hx
      exact hes.subset (e.map_target hx)
    rw [inter_eq_left.mpr hsub, het]
  exact ⟨f, hfs, hft,
    he.comp ((ambientPartialDiffeomorph U W D).symm.contMDiffOn.mono inter_subset_left)
      inter_subset_right,
    (ambientPartialDiffeomorph U W D).contMDiffOn.comp
      (hei.mono inter_subset_left) inter_subset_right⟩



def projective_cover_of_open_diffeomorph
    (U W : Opens M) (D : Diffeomorph (𝓡 3) (𝓡 3) U W ∞)
    {p : RealProjectiveThree} (S : StandardPuncturedProjectiveCover M p (U : Set M)) :
    StandardPuncturedProjectiveCover M p (W : Set M) := by
  let d := ambientPartialDiffeomorph U W D
  have hsource (x : UnitThreeSphere) (hx : Quotient.mk' x ≠ p) : S.cover x ∈ d.source :=
    S.image_eq.subset (mem_image_of_mem S.cover hx)
  refine {
    cover := d ∘ S.cover
    image_eq := ?_
    fibers := ?_
    local_diffeomorph := fun x =>
      (S.local_diffeomorph x).comp (𝓡 3) M
        (d.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hsource x x.property)) }
  · rw [image_comp, S.image_eq]
    exact d.toPartialEquiv.image_source_eq_target
  · intro x y hx hy
    change d (S.cover x) = d (S.cover y) ↔ _
    constructor
    · intro h
      exact (S.fibers x y hx hy).mp (d.toPartialEquiv.injOn (hsource x hx) (hsource y hy) h)
    · intro h
      exact congrArg d ((S.fibers x y hx hy).mpr h)

end PoincareConjecture.ClosedModels
