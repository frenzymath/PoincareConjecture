import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Models
import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Cylinder and sphere-bundle models

Adapted from Mapher, `PoincareMT/Definitions/Ch09/NeckCapTopology.lean`, commit
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained.
The standard projective and closed-component models are imported from the
canonical-neighborhood model module.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

abbrev UnitCircle :=
  {x : EuclideanSpace ℝ (Fin 2) // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}

abbrev CapModel (kind : CapModelKind) (p : RealProjectiveThree) : Type u :=
  match kind with
  | .euclidean => ULift.{u} (EuclideanSpace ℝ (Fin 3))
  | .puncturedProjective => ULift.{u} (PuncturedRealProjectiveThree p)

/-- A standard smooth cylinder on the actual displayed open region. -/
structure OpenCylinderModel (U : Set M) where
  homeomorph : (UnitTwoSphere × Set.Ioo (0 : ℝ) 1) ≃ₜ U
  coordinate : RoundCylinderSpace → M
  coordinate_eq : ∀ z : UnitTwoSphere × Set.Ioo (0 : ℝ) 1,
    homeomorph z = coordinate (z.1, (z.2 : ℝ))
  coordinate_smooth : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate
    (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)
  inverse : M → RoundCylinderSpace
  inverse_mem : ∀ x ∈ U, inverse x ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1
  left_inverse : Set.LeftInvOn inverse coordinate (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1)
  right_inverse : Set.LeftInvOn coordinate inverse U
  inverse_smooth : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ inverse U

def OpenCylinderModel.tail {U : Set M} (T : OpenCylinderModel U)
    (side : Bool) (a : ℝ) : Set M :=
  T.coordinate '' (Set.univ ×ˢ if side then Set.Ioo a 1 else Set.Ioo 0 a)

def OpenCylinderModel.middleSphere {U : Set M} (T : OpenCylinderModel U) : Set M :=
  T.coordinate '' (Set.univ ×ˢ ({1 / 2} : Set ℝ))

def SmoothSphereIsotopicIn (U S₀ S₁ : Set M) : Prop :=
  ∃ H : ℝ × UnitTwoSphere → M,
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ H
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun z ↦ H (t, z)) ∧
        Set.range (fun z ↦ H (t, z)) ⊆ U) ∧
    Set.range (fun z ↦ H (0, z)) = S₀ ∧ Set.range (fun z ↦ H (1, z)) = S₁

structure SphereBundleCircleModel where
  carrier : Type u
  carrier_topology : TopologicalSpace carrier
  carrier_charted : ChartedSpace (EuclideanSpace ℝ (Fin 3)) carrier
  carrier_manifold : IsManifold (𝓡 3) ∞ carrier
  projection : carrier → UnitCircle
  projection_continuous : Continuous projection
  projection_surjective : Function.Surjective projection
  projection_smooth : ContMDiff (𝓡 3) (𝓡 1) ∞ projection
  local_trivialization : ∀ b : UnitCircle, ∃ U : Set UnitCircle,
    IsOpen U ∧ b ∈ U ∧
      ∃ f : carrier → UnitTwoSphere × UnitCircle,
      ∃ g : UnitTwoSphere × UnitCircle → carrier,
        f '' (projection ⁻¹' U) = Set.univ ×ˢ U ∧
        Set.LeftInvOn g f (projection ⁻¹' U) ∧
        Set.LeftInvOn f g (Set.univ ×ˢ U) ∧
        ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ f (projection ⁻¹' U) ∧
        ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ g (Set.univ ×ˢ U) ∧
        ∀ x ∈ projection ⁻¹' U, (f x).2 = projection x

end PoincareMT
