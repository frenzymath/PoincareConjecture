import PoincareConjecture.Proofs.M76.Mathlib.LocallyPLProduct
import PoincareConjecture.Proofs.M76.Mathlib.PiecewiseAffineGroupoid
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false

open Set

namespace Geometry

variable {ι : Type*} [Fintype ι] {E F : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  [∀ i, FiniteDimensional ℝ (F i)]

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

theorem piecewiseAffineGroupoid_pi
    (e : ∀ i, OpenPartialHomeomorph (E i) (E i))
    (he : ∀ i, e i ∈ piecewiseAffineGroupoid (E i)) :
    OpenPartialHomeomorph.pi e ∈ piecewiseAffineGroupoid (∀ i, E i) :=
  ⟨LocallyPiecewiseAffineOn.piMap
      (fun i => (mem_piecewiseAffineGroupoid_iff (E i) (e i)).mp (he i) |>.1),
    LocallyPiecewiseAffineOn.piMap
      (fun i => (mem_piecewiseAffineGroupoid_iff (E i) (e i)).mp (he i) |>.2)⟩

end Geometry
