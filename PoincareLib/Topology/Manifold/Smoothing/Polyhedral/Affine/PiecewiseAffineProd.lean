import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FinitePLArithmetic
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PiecewiseAffineGroupoid
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Binary products of local PL maps

Two local finite certificates restrict to one finite common
neighborhood before their actual product is formed. Coordinate
projections then give binary product maps and PL groupoid
products. See Hudson pp. 15--19, Hamilton 1976, p. 66 and
M76 derivation 270.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ E]

/-- Two local PL maps on the same open source have a local
PL product on that exact source. See Hudson pp. 15--19 and
M76 derivation 270. -/
theorem LocallyPiecewiseAffineOn.prod_mk {f : E → F} {g : E → G} {U : Set E}
    (hf : LocallyPiecewiseAffineOn f U) (hg : LocallyPiecewiseAffineOn g U) :
    LocallyPiecewiseAffineOn (fun x => (f x, g x)) U := by
  intro x hx
  obtain ⟨K, hK, hxK, hKU, hfK⟩ := hf x hx
  obtain ⟨L, hL, hxL, _, hgL⟩ := hg x hx
  obtain ⟨R, hR, hxR, hRKL⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed isCompact_singleton
      (isOpen_interior.inter isOpen_interior) (singleton_subset_iff.mpr ⟨hxK, hxL⟩)
  have hRf := (hfK.finitePiecewiseAffineOn hK).restrict R hR
    (fun _ hp => interior_subset (hRKL hp).1)
  have hRg := (hgL.finitePiecewiseAffineOn hL).restrict R hR
    (fun _ hp => interior_subset (hRKL hp).2)
  obtain ⟨T, hT, hTR, hfg⟩ := hRf.prod_mk hRg
  refine ⟨T, hT, ?_, ?_, hfg⟩
  · rw [hTR]
    exact hxR (mem_singleton x)
  · rw [hTR]
    exact fun _ hp => hKU (interior_subset (hRKL hp).1)

variable [FiniteDimensional ℝ F]

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Binary products of local PL maps retain the exact
product of their open sources. See M76 derivation 270. -/
theorem LocallyPiecewiseAffineOn.prodMap {f : E → G} {g : F → H}
    {U : Set E} {V : Set F}
    (hf : LocallyPiecewiseAffineOn f U) (hg : LocallyPiecewiseAffineOn g V) :
    LocallyPiecewiseAffineOn (Prod.map f g) (U ×ˢ V) := by
  have hUV : IsOpen (U ×ˢ V) := hf.isOpen.prod hg.isOpen
  let a := (ContinuousLinearMap.fst ℝ E F).toContinuousAffineMap
  let b := (ContinuousLinearMap.snd ℝ E F).toContinuousAffineMap
  have ha := (hf.comp (locallyPiecewiseAffineOn_affine a isOpen_univ)).mono hUV
    (fun p hp => ⟨mem_univ _, hp.1⟩)
  have hb := (hg.comp (locallyPiecewiseAffineOn_affine b isOpen_univ)).mono hUV
    (fun p hp => ⟨mem_univ _, hp.2⟩)
  exact ha.prod_mk hb

/-- The binary product of two PL coordinate changes has both
local PL directions on its actual source and target. See
Hamilton p. 66 and M76 derivation 270. -/
theorem piecewiseAffineGroupoid_prod
    (e : OpenPartialHomeomorph E E) (f : OpenPartialHomeomorph F F)
    (he : e ∈ piecewiseAffineGroupoid E) (hf : f ∈ piecewiseAffineGroupoid F) :
    e.prod f ∈ piecewiseAffineGroupoid (E × F) := by
  have he' := (mem_piecewiseAffineGroupoid_iff E e).mp he
  have hf' := (mem_piecewiseAffineGroupoid_iff F f).mp hf
  exact ⟨he'.1.prodMap hf'.1, he'.2.prodMap hf'.2⟩

end Geometry
