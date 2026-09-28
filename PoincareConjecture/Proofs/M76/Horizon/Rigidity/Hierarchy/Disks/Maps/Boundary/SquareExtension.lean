import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.CircleInjectivity
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneSquareCircle
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1



theorem exists_finitePL_square_extension_of_injective_rim
    (f : V2 → V2) (hf : FinitePiecewiseAffineOn f Q)
    (hmap : MapsTo f Q Q) (hinj : InjOn f Q) :
    ∃ H : D ≃ₜ D, H.IsFinitePL ∧
      ∀ z : Q, (H ⟨z, sphere_subset_closedBall z.property⟩ : V2) = f z := by
  let r : C(Q, Q) := ⟨fun z => ⟨f z, hmap z.property⟩,
    hf.continuousOn.domRestrict.subtype_mk _⟩
  have hri : Function.Injective r := by
    intro x y hxy
    exact Subtype.ext (hinj x.property y.property (congrArg Subtype.val hxy))
  let c := HamiltonIndexOne.squareCircle
  let : Fact (0 < 4 * (2 : ℝ)) := ⟨by norm_num⟩
  let g : AddCircle (4 * (2 : ℝ)) → AddCircle (4 * (2 : ℝ)) := fun z => c.symm (r (c z))
  have hg : Continuous g := c.symm.continuous.comp (r.continuous.comp c.continuous)
  have hgi : Function.Injective g := c.symm.injective.comp (hri.comp c.injective)
  have hgs := AddCircle.surjective_of_continuous_injective hg hgi
  have hrs : Function.Surjective r := by
    intro y
    obtain ⟨x, hx⟩ := hgs (c.symm y)
    exact ⟨c x, c.symm.injective hx⟩
  have himage : f '' Q = Q := by
    apply subset_antisymm (image_subset_iff.mpr hmap)
    intro y hy
    obtain ⟨x, hx⟩ := hrs ⟨y, hy⟩
    exact ⟨x, x.property, congrArg Subtype.val hx⟩
  obtain ⟨B, hB, hBval⟩ := hf.exists_homeomorph_image hinj
  let E : Q ≃ₜ Q := B.trans (Homeomorph.setCongr himage)
  have hE : E.IsFinitePL := ⟨f, hf, fun z => hBval z⟩
  obtain ⟨H, hH, hHE, _⟩ := (isFinitePLBallPair_unit_cube (ι := Fin 2)).exists_extension
    (isFinitePLBallPair_unit_cube (ι := Fin 2)) E hE
  refine ⟨H, hH, fun z => ?_⟩
  exact (congrArg Subtype.val (hHE z)).trans (hBval z)

end PoincareConjecture.M76
