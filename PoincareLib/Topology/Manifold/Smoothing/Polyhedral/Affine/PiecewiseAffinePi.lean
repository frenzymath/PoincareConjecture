import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.LocallyPLProduct
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.PiecewiseAffineGroupoid
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Finite products of PL coordinate changes

Each coordinate map is composed with its actual continuous
linear projection. A common finite source subdivision gives
the product formula, including empty products. This supplies
the standard torus charts in Hamilton 1976, pp. 64--67;
see M76 derivation 270.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {ι : Type*} [Fintype ι] {E F : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i, FiniteDimensional ℝ (F i)]

/-- The finite product of local PL maps is locally PL on the
actual product of their open sources. Empty products are
included. See Hamilton pp. 64--67 and M76 derivation 270. -/
theorem LocallyPiecewiseAffineOn.piMap {f : ∀ i, E i → F i} {U : ∀ i, Set (E i)}
    (hf : ∀ i, LocallyPiecewiseAffineOn (f i) (U i)) :
    LocallyPiecewiseAffineOn (fun x i => f i (x i)) (Set.pi univ U) := by
  have hU : IsOpen (Set.pi univ U) :=
    isOpen_set_pi finite_univ (fun i _ => (hf i).isOpen)
  apply LocallyPiecewiseAffineOn.pi hU
  intro i
  let p : (∀ j, E j) →ᴬ[ℝ] E i :=
    (ContinuousLinearMap.proj i).toContinuousAffineMap
  have hp := locallyPiecewiseAffineOn_affine p isOpen_univ
  exact ((hf i).comp hp).mono hU (fun x hx => ⟨mem_univ x, hx i (mem_univ i)⟩)

/-- Finite products of PL open partial homeomorphisms remain
in the actual product-space PL groupoid. Both directions
retain finite local formulas. See Hamilton pp. 64--67 and
M76 derivation 270. -/
theorem piecewiseAffineGroupoid_pi
    (e : ∀ i, OpenPartialHomeomorph (E i) (E i))
    (he : ∀ i, e i ∈ piecewiseAffineGroupoid (E i)) :
    OpenPartialHomeomorph.pi e ∈ piecewiseAffineGroupoid (∀ i, E i) :=
  ⟨LocallyPiecewiseAffineOn.piMap
      (fun i => (mem_piecewiseAffineGroupoid_iff (E i) (e i)).mp (he i) |>.1),
    LocallyPiecewiseAffineOn.piMap
      (fun i => (mem_piecewiseAffineGroupoid_iff (E i) (e i)).mp (he i) |>.2)⟩

end Geometry
