import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.Parameterization
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Algebra.Structures

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem halfAxial_smooth (side : Bool) (a : ℝ) :
    ContMDiff CylModel CylModel ∞
      (fun z : RoundCylinderSpace => (z.1, halfAxial side a z.2)) := by
  cases side
  · exact contMDiff_fst.prodMk (contMDiff_const.mul (contMDiff_const.sub contMDiff_snd))
  · exact contMDiff_fst.prodMk (contMDiff_const.add (contMDiff_const.mul contMDiff_snd))

theorem halfAxialInverse_smooth (side : Bool) (a : ℝ) :
    ContMDiff CylModel CylModel ∞
      (fun z : RoundCylinderSpace => (z.1, halfAxialInverse side a z.2)) := by
  cases side
  · exact contMDiff_fst.prodMk
      (contMDiff_const.sub (contMDiff_snd.mul contMDiff_const))
  · exact contMDiff_fst.prodMk
      ((contMDiff_snd.sub contMDiff_const).mul contMDiff_const)

theorem halfAxial_collar (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Ioo (-r) 1, halfAxial side a t ∈ Ioo (0 : ℝ) 1 := by
  let r := min a (1 - a) / 2
  have hr : 0 < r := div_pos (lt_min ha.1 (sub_pos.mpr ha.2)) (by norm_num)
  have hra : r < a := by dsimp [r]; linarith [min_le_left a (1 - a), ha.1]
  have hra' : r < 1 - a := by dsimp [r]; linarith [min_le_right a (1 - a), ha.2]
  refine ⟨r, hr, fun t ht => ?_⟩
  cases side
  · change 0 < a * (1 - t) ∧ a * (1 - t) < 1
    refine ⟨mul_pos ha.1 (sub_pos.mpr ht.2), ?_⟩
    have h := mul_lt_mul_of_pos_left ht.1 ha.1
    have har := mul_lt_mul_of_pos_right ha.2 hr
    nlinarith
  · change 0 < a + (1 - a) * t ∧ a + (1 - a) * t < 1
    constructor
    · have h := mul_lt_mul_of_pos_left ht.1 (sub_pos.mpr ha.2)
      have hmr := mul_lt_mul_of_pos_right (show 1 - a < 1 by linarith [ha.1]) hr
      nlinarith
    · have h := mul_lt_mul_of_pos_left ht.2 (sub_pos.mpr ha.2)
      nlinarith

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}

noncomputable def halfOpenPartialHomeomorph (Q : OpenCylinderModel U) (hU : IsOpen U)
    (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    OpenPartialHomeomorph RoundCylinderSpace M where
  toFun := Q.halfParameterization side a
  invFun x := ((Q.inverse x).1, halfAxialInverse side a (Q.inverse x).2)
  source := {z | halfAxial side a z.2 ∈ Ioo (0 : ℝ) 1}
  target := U
  map_source' z hz := Q.coordinate_mem ⟨mem_univ _, hz⟩
  map_target' x hx := by
    change halfAxial side a (halfAxialInverse side a (Q.inverse x).2) ∈ Ioo (0 : ℝ) 1
    rw [halfAxial_right_inverse side ha]
    exact (Q.inverse_mem x hx).2
  left_inv' z hz := by
    have hdom : (z.1, halfAxial side a z.2) ∈ univ ×ˢ Ioo (0 : ℝ) 1 :=
      ⟨mem_univ _, hz⟩
    change ((Q.inverse (Q.coordinate (z.1, halfAxial side a z.2))).1,
      halfAxialInverse side a (Q.inverse (Q.coordinate (z.1, halfAxial side a z.2))).2) = z
    rw [Q.left_inverse hdom, halfAxial_left_inverse side ha]
  right_inv' x hx := by
    change Q.coordinate ((Q.inverse x).1,
      halfAxial side a (halfAxialInverse side a (Q.inverse x).2)) = x
    rw [halfAxial_right_inverse side ha]
    exact Q.right_inverse hx
  open_source := isOpen_Ioo.preimage (halfAxial_smooth side a).continuous.snd
  open_target := hU
  continuousOn_toFun := Q.coordinate_smooth.continuousOn.comp
    (halfAxial_smooth side a).continuous.continuousOn (fun z hz => ⟨mem_univ _, hz⟩)
  continuousOn_invFun := (halfAxialInverse_smooth side a).continuous.comp_continuousOn
    Q.inverse_smooth.continuousOn

theorem halfOpenPartialHomeomorph_mdifferentiable
    (Q : OpenCylinderModel U) (hU : IsOpen U)
    (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    (Q.halfOpenPartialHomeomorph hU side ha).MDifferentiable CylModel (𝓡 3) := by
  constructor
  · exact (Q.coordinate_smooth.comp (halfAxial_smooth side a).contMDiffOn
      (fun z hz => ⟨mem_univ _, hz⟩)).mdifferentiableOn (by simp)
  · exact ((halfAxialInverse_smooth side a).comp_contMDiffOn
      Q.inverse_smooth).mdifferentiableOn (by simp)

theorem halfParameterization_regular (Q : OpenCylinderModel U) (hU : IsOpen U)
    (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ico (0 : ℝ) 1) :
    Function.Bijective (mfderiv CylModel (𝓡 3) (Q.halfParameterization side a) z) :=
  (Q.halfOpenPartialHomeomorph_mdifferentiable hU side ha).mfderiv_bijective
    (halfAxial_mem_open side ha hz)

theorem halfParameterization_smooth_collar (Q : OpenCylinderModel U)
    (side : Bool) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ r : ℝ, 0 < r ∧ ContMDiffOn CylModel (𝓡 3) ∞
      (Q.halfParameterization side a) (univ ×ˢ Ioo (-r) 1) := by
  obtain ⟨r, hr, hmap⟩ := halfAxial_collar side ha
  exact ⟨r, hr, Q.coordinate_smooth.comp (halfAxial_smooth side a).contMDiffOn
    (fun z hz => ⟨mem_univ _, hmap z.2 hz.2⟩)⟩

end PoincareConjecture.OpenCylinderModel
