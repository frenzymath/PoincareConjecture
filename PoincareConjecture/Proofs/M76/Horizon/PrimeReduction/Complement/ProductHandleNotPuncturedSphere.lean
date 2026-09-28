import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.HandleLoopObstruction
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.PuncturedSphereCircleExtension

set_option autoImplicit false

open Set Geometry
open scoped unitInterval

namespace Poincare.Topology

local notation "V3" => (Fin 3 → ℝ)
local notation "V4" => (Fin 4 → ℝ)
local notation "Sphere" => Geometry.CubicalThreeSphere.sphere
local notation "Circle" => AddCircle (1 : ℝ)

variable {E Y ι : Type*} [TopologicalSpace E] [TopologicalSpace Y]
  [Nonempty Y] [Finite ι]

theorem not_nonempty_homeomorph_punctured_sphere_of_product_handle
    {P H : Set E} (hP : IsClosed P) (hH : IsClosed H) (hPc : IsPathConnected P)
    (C : (Y × unitInterval) ≃ₜ H)
    (hattach : ∀ z : Y × unitInterval,
      (C z : E) ∈ P ↔ z.2 = 0 ∨ z.2 = 1)
    (D B : ι → Set V4) (hD : ∀ i, IsFinitePLBallPair V3 (D i) (B i))
    (hDS : ∀ i, D i ⊆ Sphere)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hopen : ∀ i, IsOpen ((Subtype.val : Sphere → V4) ⁻¹' (D i \ B i))) :
    ¬ Nonempty ((P ∪ H : Set E) ≃ₜ (Sphere \ ⋃ i, D i \ B i : Set V4)) := by
  rintro ⟨e⟩
  obtain ⟨f, _, _, x, hx, gamma, hperiod, _⟩ :=
    exists_nontrivial_loop_of_product_handle hP hH hPc C hattach
  let eC : C((P ∪ H : Set E), (Sphere \ ⋃ i, D i \ B i : Set V4)) :=
    ⟨e, e.continuous⟩
  let f' : C((Sphere \ ⋃ i, D i \ B i : Set V4), Circle) :=
    f.comp ⟨e.symm, e.symm.continuous⟩
  have hcomp : f'.comp eC = f := by
    ext y
    exact congrArg f (e.symm_apply_apply y)
  have hnull := Geometry.CubicalThreeSphere.circle_map_loop_nullhomotopic_of_isOpen
    D B hD hDS hdis hopen f' (e x) (gamma.map e.continuous)
  rw [Path.map_map] at hnull
  change (gamma.map (f'.comp eC).continuous).Homotopic
    (Path.refl ((f'.comp eC) x)) at hnull
  rw [hcomp] at hnull
  have hcast := hnull.pathCast hx.symm hx.symm
  have hrefl : (Path.refl (f x)).cast hx.symm hx.symm = Path.refl 0 := by
    ext t
    exact hx
  rw [hrefl] at hcast
  exact AddCircle.periodLoop_not_homotopic_refl 1 (hperiod.symm.trans hcast)

end Poincare.Topology
