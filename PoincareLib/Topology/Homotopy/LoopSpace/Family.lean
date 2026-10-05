import PoincareLib.Topology.Homotopy.LoopSpace.Basic

/-!
# Sphere families in the C1 free-loop space

Adapted from Mapher commit f927d9e1f0810042766d3b5f64d3f4da02ee93cc.
Source: Morgan--Tian, Definition 18.17 and Lemma 18.27, pp. 430, 434-435.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Bundle Topology ENNReal unitInterval
universe u
namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- A concrete realization of a free sphere family's based `π₂` class.  The
cube representative is a genuine `GenLoop`, and the sphere parameterization
ties it to the displayed family. The selected parameterization, including its
orientation, is part of the data; a raw sphere map alone does not specify the
decorated family's based class. -/
structure FreeTwoSphereClassCertificate
    (basepoint : M)
    (family : LoopTwoSphere → C1FreeLoopSpace (M := M))
    (α : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
      (constantC1Loop basepoint)) where
  cube_representative : ContinuousMap (Fin 2 → I) (C1FreeLoopSpace (M := M))
  boundary_const : ∀ y ∈ Cube.boundary (Fin 2),
    cube_representative y = constantC1Loop basepoint
  sphere_parameter : ContinuousMap (Fin 2 → I) LoopTwoSphere
  sphere_parameter_surjective : Function.Surjective sphere_parameter
  sphere_parameter_boundary_collapsed : ∃ c : LoopTwoSphere, ∀ y,
    y ∈ Cube.boundary (Fin 2) → sphere_parameter y = c
  /-- Exact fibers identify all boundary points and no distinct interior points. -/
  sphere_parameter_quotient_fiber : ∀ y z,
    sphere_parameter y = sphere_parameter z ↔
      y = z ∨ (y ∈ Cube.boundary (Fin 2) ∧ z ∈ Cube.boundary (Fin 2))
  family_agreement : ∀ y,
    cube_representative y = family (sphere_parameter y)
  class_eq : α = Quotient.mk'
    (⟨cube_representative, boundary_const⟩ :
      GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop basepoint))

/-- A free two-sphere family of null-homotopic C¹ loops. -/
structure FreeTwoSphereFamily where
  /-- Basepoint used for the based loop-space class of the family. -/
  basepoint : M
  family : LoopTwoSphere → C1FreeLoopSpace (M := M)
  /-- The typed based `π₂(ΛM, *)` class represented by this family. -/
  homotopy_class : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
    (constantC1Loop basepoint)
  class_certificate : FreeTwoSphereClassCertificate basepoint family homotopy_class
  continuous : Continuous family
  derivative_continuous : ∀ i : Fin 2,
    Continuous (fun p : LoopTwoSphere × LoopCircle =>
      c1LoopDerivative (family p.1) p.2 i)
  null_homotopic : ∀ c, IsNullHomotopicLoop (family c)
  joint_extension : ∃ extension : LoopTwoSphere × LoopPlane → M,
    ContinuousOn extension (Set.univ ×ˢ loopAnnulus) ∧
      (∀ c (z : LoopCircle), extension (c, z.1) = family c z) ∧
      ∀ c, ContMDiffOn (𝓡 2) (𝓡 3) 1 (fun z => extension (c, z)) loopAnnulus

/-- The dependent sigma value of a family's based homotopy class. -/
def familySigmaClass (Γ : FreeTwoSphereFamily (M := M)) :
    Σ x : M, HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M))
      (constantC1Loop x) :=
  ⟨Γ.basepoint, Γ.homotopy_class⟩

/-- Free homotopy of sphere families, with a continuous family of families. -/
def FreeTwoSphereHomotopic (Γ₁ Γ₂ : FreeTwoSphereFamily (M := M)) : Prop :=
  ∃ H : Set.Icc (0 : ℝ) 1 → FreeTwoSphereFamily,
    Γ₁.basepoint = Γ₂.basepoint ∧
      familySigmaClass Γ₁ = familySigmaClass Γ₂ ∧
      (∀ s, (H s).basepoint = Γ₁.basepoint) ∧
      Continuous (fun p : Set.Icc (0 : ℝ) 1 × LoopTwoSphere => (H p.1).family p.2) ∧
      H ⟨0, by simp⟩ = Γ₁ ∧ H ⟨1, by simp⟩ = Γ₂


/-- The raw constant-loop family used by the free-loop reformulation of
Lemma 18.27. -/
noncomputable def constantLoopFamily {M : Type u} [TopologicalSpace M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] (x : M) :
    ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M)) :=
  ⟨fun _ => constantC1Loop x, continuous_const⟩

end PoincareMT
