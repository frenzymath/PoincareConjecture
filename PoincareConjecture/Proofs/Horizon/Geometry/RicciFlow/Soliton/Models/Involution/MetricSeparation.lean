import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Cylinder

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace SphereLineProductData

variable {P : Type u} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) P] [IsManifold (𝓡 3) ∞ P]

theorem surface_inner_time_scaling (d : SphereLineProductData (P := P))
    (t : ℝ) (ht : t < 0) :
    letI := d.surface_topology
    letI := d.surface_charted
    letI := d.surface_manifold
    ∀ p : d.surface, ∀ v w : TangentSpace (𝓡 2) p,
      (d.surface_metric t).inner p v w =
        (-t) * (d.surface_metric (-1)).inner p v w := by
  letI := d.surface_topology
  letI := d.surface_charted
  letI := d.surface_manifold
  intro p v w
  rw [d.surface_inner_round t ht, d.surface_inner_round (-1) (by norm_num)]
  ring

theorem product_inner_time_scaling (d : SphereLineProductData (P := P))
    (t : ℝ) (ht : t < 0) :
    letI := d.surface_topology
    letI := d.surface_charted
    letI := d.surface_manifold
    letI := d.product_charted
    letI := d.product_manifold
    ∀ p : d.surface × ℝ, ∀ v w : TangentSpace (𝓡 3) p,
      (d.product_metric t).inner p v w =
        (-t) * (d.surface_metric (-1)).inner p.1
          (d.tangent_surface_component p v) (d.tangent_surface_component p w) +
      d.tangent_line_component p v * d.tangent_line_component p w := by
  letI := d.surface_topology
  letI := d.surface_charted
  letI := d.surface_manifold
  letI := d.product_charted
  letI := d.product_manifold
  intro p v w
  rw [d.product_inner_formula t ht, d.surface_inner_time_scaling t ht]

end SphereLineProductData

namespace QuotientSphereLineCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}

theorem involution_preserves_tangent_forms (q : QuotientSphereLineCertificate G) :
    letI := q.cover_topology
    letI := q.cover_charted
    letI := q.cover_manifold
    letI := q.product.surface_topology
    letI := q.product.surface_charted
    letI := q.product.surface_manifold
    letI := q.product.product_charted
    letI := q.product.product_manifold
    ∀ p : q.product.surface × ℝ, ∀ v w : TangentSpace (𝓡 3) p,
      let v' := mfderiv (𝓡 3) (𝓡 3) q.involution p v
      let w' := mfderiv (𝓡 3) (𝓡 3) q.involution p w
      (q.product.surface_metric (-1)).inner p.1
          (q.product.tangent_surface_component p v)
          (q.product.tangent_surface_component p w) =
        (q.product.surface_metric (-1)).inner (q.involution p).1
          (q.product.tangent_surface_component (q.involution p) v')
          (q.product.tangent_surface_component (q.involution p) w') ∧
      q.product.tangent_line_component p v * q.product.tangent_line_component p w =
        q.product.tangent_line_component (q.involution p) v' *
          q.product.tangent_line_component (q.involution p) w' := by
  letI := q.cover_topology
  letI := q.cover_charted
  letI := q.cover_manifold
  letI := q.product.surface_topology
  letI := q.product.surface_charted
  letI := q.product.surface_manifold
  letI := q.product.product_charted
  letI := q.product.product_manifold
  intro p v w
  have h₁ := q.involution_isometry (-1) (by norm_num) p v w
  have h₂ := q.involution_isometry (-2) (by norm_num) p v w
  simp only [q.product.product_inner_time_scaling (-1) (by norm_num),
    q.product.product_inner_time_scaling (-2) (by norm_num)] at h₁ h₂
  dsimp only
  constructor <;> linarith

end QuotientSphereLineCertificate

end PoincareConjecture
