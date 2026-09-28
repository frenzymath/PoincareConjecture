import PoincareConjecture.Proofs.M76.Mathlib.HeightPlaneAffineCoordinates
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Convex.Intrinsic

set_option autoImplicit false

open Set Module

namespace AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_defining_height_of_finrank_two
    (P : AffineSubspace ℝ E) (hdim : finrank ℝ E = 3)
    (hP : finrank ℝ P.direction = 2) (hne : (P : Set E).Nonempty) :
    ∃ A : E →ᵃ[ℝ] ℝ, A.linear ≠ 0 ∧ ∀ x, A x = 0 ↔ x ∈ P := by
  obtain ⟨p, hp⟩ := hne
  have hdir : P.direction < ⊤ := lt_top_iff_ne_top.mpr (by
    intro h
    rw [h, finrank_top, hdim] at hP
    omega)
  obtain ⟨l, hl, hPl⟩ := P.direction.exists_le_ker_of_lt_top hdir
  have hkerdim := Module.Dual.finrank_ker_add_one_of_ne_zero hl
  have hker : P.direction = LinearMap.ker l :=
    Submodule.eq_of_le_of_finrank_eq hPl (by omega)
  let T := ContinuousAffineEquiv.constVAdd ℝ E (-p)
  let A : E →ᵃ[ℝ] ℝ := l.toAffineMap.comp T.toAffineEquiv.toAffineMap
  have hAx (x : E) : A x = l (x - p) := by
    change l (-p + x) = l (x - p)
    congr 1
    abel
  refine ⟨A, ?_, fun x => ?_⟩
  · change l.comp (LinearMap.id) ≠ 0
    simpa using hl
  · rw [hAx, ← LinearMap.mem_ker, ← hker]
    constructor
    · intro hx
      have h := P.vadd_mem_of_mem_direction hx hp
      simpa only [vadd_eq_add, sub_add_cancel] using h
    · intro hx
      exact P.vsub_mem_direction hx hp

omit [FiniteDimensional ℝ E] in

theorem exists_nonzero_height_vertex_of_span_union_eq_top
    (P : AffineSubspace ℝ E) (hP : P ≠ ⊤)
    (A : E →ᵃ[ℝ] ℝ) (hA : ∀ x, A x = 0 ↔ x ∈ P)
    {s t : Finset E} (htP : (t : Set E) ⊆ P)
    (hspan : affineSpan ℝ ((s : Set E) ∪ (t : Set E)) = ⊤) :
    ∃ v ∈ s, A v ≠ 0 := by
  by_contra! hzero
  have hsP : (s : Set E) ⊆ P := fun x hx => (hA x).mp (hzero x hx)
  have hle := affineSpan_le.mpr (union_subset hsP htP)
  rw [hspan] at hle
  exact hP (top_le_iff.mp hle)

end AffineSubspace

open Filter
open scoped Topology

namespace Set

theorem eventually_mem_iff_mem_affineSpan_of_intrinsicInterior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {p : E} (hp : p ∈ intrinsicInterior ℝ S) :
    ∀ᶠ x in 𝓝 p, x ∈ S ↔ x ∈ affineSpan ℝ S := by
  obtain ⟨q, hq, hqp⟩ := mem_intrinsicInterior.mp hp
  obtain ⟨U, hU, hUeq⟩ := isOpen_induced_iff.mp
    (isOpen_interior : IsOpen (interior
      ((Subtype.val : affineSpan ℝ S → E) ⁻¹' S)))
  have hpU : p ∈ U := by
    rw [← hqp]
    exact hUeq.symm.subset hq
  filter_upwards [hU.mem_nhds hpU] with x hx
  refine ⟨fun hxS => subset_affineSpan ℝ S hxS, fun hxspan => ?_⟩
  have hxi : (⟨x, hxspan⟩ : affineSpan ℝ S) ∈
      interior ((Subtype.val : affineSpan ℝ S → E) ⁻¹' S) := hUeq.subset hx
  exact (show (⟨x, hxspan⟩ : affineSpan ℝ S) ∈
    (Subtype.val : affineSpan ℝ S → E) ⁻¹' S from interior_subset hxi)

end Set
