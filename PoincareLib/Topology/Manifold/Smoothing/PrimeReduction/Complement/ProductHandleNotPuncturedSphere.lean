import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Complement.HandleLoopObstruction
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Complement.PuncturedSphereCircleExtension

/-!
# A product handle cannot be a punctured standard sphere

The actual handle loop has a nonzero circle winding. Every circle map
on a sphere with finitely many disjoint actual PL-ball interiors removed
extends over those balls, so its loops have zero winding. Transport through
a purported homeomorphism gives the contradiction, without a supplied
classification or no-L3 assertion.
-/

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

/-- Gluing both end disks of an actual product handle to a single
path-connected closed carrier cannot produce any of the literal punctured
standard sphere models. No identification of a disk-port quotient with this
handle carrier is included in the hypotheses or conclusion. -/
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
