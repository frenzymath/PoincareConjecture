import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryBoundary

set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

structure BoundaryMotionHistory {X : Type*} [TopologicalSpace X]
    (g : V2 → X) (T : OpenPartialHomeomorph X V3) (c : V3 ≃L[ℝ] C3)
    (J C₀ B : SimplicialComplex ℝ V3) (q : V3 → V2) (ε : ℝ)
    (H : PLCarrierMotion J.space C₀.space ε) where
  ambient : SimplicialComplex ℝ V3
  sheet : SimplicialComplex ℝ V3
  parameter : V3 → V2
  radius : ℝ
  radius_pos : 0 < radius
  closed_support : closedBall (0 : V3) radius ⊆ interior J.space
  protected_space : C₀.space = sheet.space \ ball (0 : V3) radius
  ambient_finite : ambient.faces.Finite
  ambient_subdivision : ambient.IsSubdivision J
  sheet_subcomplex : sheet ≤ ambient
  sheet_space : sheet.space = T '' (g '' D ∩ T.source) ∩ J.space
  parameter_affine : sheet.AffineOnFaces parameter
  parameter_injective : InjOn parameter sheet.space
  parameter_inside : MapsTo parameter sheet.space D
  parameter_right : ∀ z ∈ sheet.space,
    g (parameter z) ∈ T.source ∧ T (g (parameter z)) = z
  parameter_left : ∀ x ∈ D, g x ∈ T.source → T (g x) ∈ J.space →
    parameter (T (g x)) = x
  parameter_rim : ∀ z ∈ sheet.space, (c z).1.1 = 0 ↔ parameter z ∈ Rim
  motion_affine : ambient.AffineOnFaces (H.map 1)
  region_height : ∀ u z, (c (H.map u z)).1.1 = (c z).1.1
  strict_signs : ∀ v ∈ ambient.vertices, (c v).2 ≠ 0 → ∀ u,
    (0 < (c (H.map u v)).2 ↔ 0 < (c v).2) ∧
    ((c (H.map u v)).2 < 0 ↔ (c v).2 < 0)
  zero_faces : ∀ face ∈ sheet.faces,
    (∀ v ∈ face, (c (H.map 1 v)).2 = 0) → ∀ v ∈ face, (c v).2 = 0
  endpoint_faces : B.faces = (fun face => face.image (H.map 1)) '' sheet.faces
  endpoint_parameter : q = parameter ∘ (H.map 1).symm

end Geometry.OriginalPLTower
