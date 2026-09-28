import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.EmbeddedSurfaceCount
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedAffineHomeomorph
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false

open Set

namespace AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_planar_affine_injection (P : AffineSubspace ℝ E)
    (hP : Module.finrank ℝ P.direction ≤ 2) (hne : (P : Set E).Nonempty) :
    ∃ f : E →ᴬ[ℝ] (Fin 2 → ℝ), InjOn f P := by
  classical
  obtain ⟨p, hp⟩ := hne
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl P.direction
  obtain ⟨g, hg⟩ := (finrank_le_iff_exists_linearMap (R := ℝ)
    (M := P.direction) (M' := Fin 2 → ℝ)).mp (by simpa using hP)
  let L := g.comp (P.direction.projectionOnto W hW)
  let f : E →ᵃ[ℝ] (Fin 2 → ℝ) := L.toAffineMap.comp (AffineEquiv.constVAdd ℝ E (-p)).toAffineMap
  refine ⟨⟨f, f.continuous_of_finiteDimensional⟩, ?_⟩
  intro x hx y hy hxy
  have hxP : x - p ∈ P.direction := P.vsub_mem_direction hx hp
  have hyP : y - p ∈ P.direction := P.vsub_mem_direction hy hp
  change g (P.direction.projectionOnto W hW (-p + x)) =
    g (P.direction.projectionOnto W hW (-p + y)) at hxy
  rw [add_comm (-p), ← sub_eq_add_neg, add_comm (-p), ← sub_eq_add_neg,
    Submodule.projectionOnto_apply_of_mem_left hW hxP,
    Submodule.projectionOnto_apply_of_mem_left hW hyP] at hxy
  exact sub_left_injective (congrArg Subtype.val (hg hxy))

end AffineSubspace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem surfaceEulerCount_eq_one_of_convex_low_dimension
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hc : Convex ℝ K.space) (hne : K.space.Nonempty)
    (P : AffineSubspace ℝ E) (hKP : K.space ⊆ P)
    (hdim : Module.finrank ℝ P.direction ≤ 2) :
    K.surfaceEulerCount = 1 := by
  obtain ⟨f, hf⟩ := P.exists_planar_affine_injection hdim (hne.mono hKP)
  let hfaces := K.affineOnFaces_affine f
  let hinj := hf.mono hKP
  let J := hfaces.embeddedImage hinj
  let : Nonempty K.space := hne.to_subtype
  let : ContractibleSpace K.space := hc.contractibleSpace hne
  let : ContractibleSpace J.space := (hfaces.embeddedHomeomorph hinj hK).symm.contractibleSpace
  rw [← hfaces.surfaceEulerCount_embeddedImage hinj]
  exact J.surfaceEulerCount_eq_one_of_planar_contractible (by simp)
    (hfaces.embeddedImage_finite hinj hK)

theorem surfaceEulerCount_eq_one_of_small_convexHull
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (s : Finset E) (hne : s.Nonempty) (hcard : s.card ≤ 3)
    (hspace : K.space = convexHull ℝ (s : Set E)) :
    K.surfaceEulerCount = 1 := by
  classical
  let : Nonempty s := hne.to_subtype
  have hrank := finrank_vectorSpan_range_add_one_le ℝ ((↑) : s → E)
  have hrange : range ((↑) : s → E) = (s : Set E) := by ext; simp
  rw [hrange, Fintype.card_coe] at hrank
  apply K.surfaceEulerCount_eq_one_of_convex_low_dimension hK
    (hspace ▸ convex_convexHull ℝ _) ?_ (affineSpan ℝ (s : Set E)) ?_ ?_
  · rw [hspace]
    obtain ⟨p, hp⟩ := hne
    exact ⟨p, subset_convexHull ℝ _ hp⟩
  · rw [hspace]
    exact convexHull_subset_affineSpan _
  · rw [direction_affineSpan]
    omega

end Geometry.SimplicialComplex
