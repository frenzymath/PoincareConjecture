import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalFinitePLSphereCut









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

structure OriginalFiniteSphereCollar {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) (R S O : Set X) (B : Bool → Set X) where
  parameters : Finset R
  complex : SimplicialComplex ℝ (parameters → ℝ × V3)
  finite : complex.faces.Finite
  parametrization : complex.space ≃ₜ S
  map : (parameters → ℝ × V3) × ℝ → X
  width : ℝ
  width_pos : 0 < width
  width_le : width ≤ 1 / 4
  pl : PolyhedralPLInCharts e map (complex.space ×ˢ Icc (-1 : ℝ) 1)
  embedding : Topology.IsEmbedding
    (fun z : (complex.space ×ˢ Icc (-1 : ℝ) 1 : Set ((parameters → ℝ × V3) × ℝ)) => map z)
  center : ∀ x : complex.space, map ((x : parameters → ℝ × V3), 0) = parametrization x
  open_eq : O = map '' (complex.space ×ˢ Ioo (-width) width)
  closed_eq : closure O = map '' (complex.space ×ˢ Icc (-width) width)
  isOpen : IsOpen O
  closedInterior : map '' (complex.space ×ˢ Icc (-width) width) ⊆ interior R
  endpoint_eq : ∀ b, B b = map '' (complex.space ×ˢ {if b then width else -width})
  endpointMap : ∀ b, S ≃ₜ B b
  endpoint_value : ∀ b (x : S), (endpointMap b x : X) =
    map (((parametrization.symm x : complex.space) : parameters → ℝ × V3),
      if b then width else -width)

end PoincareConjecture.M76
