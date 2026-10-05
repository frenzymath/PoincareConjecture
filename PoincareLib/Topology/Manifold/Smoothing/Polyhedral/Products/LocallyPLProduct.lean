import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.FinitePLProduct
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.LocallyPiecewiseAffine

/-!
# Finite products of local PL formulas

Intersect the finitely many coordinate neighborhoods and pass
to one finite carrier before forming a common source subdivision.
See Hudson 1969, pp. 12--19, Hamilton 1976, p. 69 and M76
derivation 258.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite product of locally PL maps is locally PL on their
common open source. Openness is explicit because an empty
coordinate family supplies no source information. See Hudson
pp. 12--19 and M76 derivation 258. -/
theorem LocallyPiecewiseAffineOn.pi
    {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i, FiniteDimensional ℝ (F i)] {f : ∀ i, E → F i} {U : Set E}
    (hU : IsOpen U) (hf : ∀ i, LocallyPiecewiseAffineOn (f i) U) :
    LocallyPiecewiseAffineOn (fun x i => f i x) U := by
  classical
  intro x hx
  choose K hK hxK hKU hfK using fun i => hf i x hx
  let V : Set E := U ∩ ⋂ i, interior (K i).space
  have hV : IsOpen V := hU.inter (isOpen_iInter_of_finite fun _ => isOpen_interior)
  have hxV : x ∈ V := ⟨hx, mem_iInter.mpr hxK⟩
  obtain ⟨L, hL, hxL, hLV⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed
      isCompact_singleton hV (singleton_subset_iff.mpr hxV)
  have hfi (i : ι) : FinitePiecewiseAffineOn (f i) L.space :=
    (hfK i).finitePiecewiseAffineOn (hK i) |>.restrict L hL
      (fun _ hy => interior_subset (mem_iInter.mp (hLV hy).2 i))
  obtain ⟨R, hR, hRL, hfR⟩ := FinitePiecewiseAffineOn.pi_on_complex L hL hfi
  refine ⟨R, hR, ?_, ?_, hfR⟩
  · rw [hRL]
    exact hxL (mem_singleton x)
  · rw [hRL]
    exact fun _ hy => (hLV hy).1

end Geometry
