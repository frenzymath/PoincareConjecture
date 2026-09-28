import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Cylinder











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SphereLineProductData

variable {M P : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) P]
  [IsManifold (𝓡 3) ∞ P]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)
  (d : SphereLineProductData (P := P))

local instance : TopologicalSpace d.surface := d.surface_topology
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (d.surface × ℝ) :=
  d.product_charted
local instance : IsManifold (𝓡 3) ∞ (d.surface × ℝ) := d.product_manifold



def quotientCertificateOfProjection
    (τ : d.surface × ℝ → d.surface × ℝ)
    (hτ : ContMDiff (𝓡 3) (𝓡 3) ∞ τ)
    (hττ : Function.Involutive τ) (hfree : ∀ p, τ p ≠ p)
    (q : d.surface × ℝ → M) (hq : ContMDiff (𝓡 3) (𝓡 3) ∞ q)
    (hsurj : Function.Surjective q)
    (hfiber : ∀ p z, q p = q z ↔ z = p ∨ z = τ p)
    (hmetric : ∀ t : ℝ, t < 0 → ∀ p : d.surface × ℝ,
      ∀ v w : TangentSpace (𝓡 3) p,
        (d.product_metric t).inner p v w = (G.flow.metric t).inner (q p)
          (mfderiv (𝓡 3) (𝓡 3) q p v) (mfderiv (𝓡 3) (𝓡 3) q p w)) :
    QuotientSphereLineCertificate G := by
  have hcomp : q ∘ τ = q := funext fun p =>
    ((hfiber p (τ p)).mpr (Or.inr rfl)).symm
  refine {
    cover := P
    cover_topology := inferInstance
    cover_charted := inferInstance
    cover_manifold := inferInstance
    product := d
    involution := τ
    involution_involutive := hττ
    involution_free := hfree
    involution_smooth := hτ
    involution_isometry := ?_
    quotient_carrier := M
    quotient_topology := inferInstance
    quotient_charted := inferInstance
    quotient_manifold := inferInstance
    quotient_map := q
    quotient_map_smooth := hq
    quotient_map_surjective := hsurj
    quotient_fiber_eq_orbit := hfiber
    quotient_flow := G.flow
    quotient_metric := G.flow.metric
    quotient_connection := G.flow.connection
    quotient_flow_metric := fun _ _ => rfl
    quotient_flow_connection := fun _ _ => HEq.rfl
    quotient_metric_pullback := hmetric
    flow_isometric_to_quotient := ?_ }
  · intro t ht p v w
    rw [hmetric t ht p, hmetric t ht (τ p)]
    calc
      (G.flow.metric t).inner (q p)
          (mfderiv (𝓡 3) (𝓡 3) q p v) (mfderiv (𝓡 3) (𝓡 3) q p w) =
          (G.flow.metric t).inner ((q ∘ τ) p)
            (mfderiv (𝓡 3) (𝓡 3) (q ∘ τ) p v)
            (mfderiv (𝓡 3) (𝓡 3) (q ∘ τ) p w) := by rw [hcomp]
      _ = _ := by
        rw [mfderiv_comp p (hq.mdifferentiable (by simp) _)
          (hτ.mdifferentiable (by simp) _)]
        rfl
  · refine ⟨Diffeomorph.refl (𝓡 3) M ∞, ?_⟩
    intro t ht p v w
    change (G.flow.metric t).inner p v w =
      (G.flow.metric t).inner p (mfderiv (𝓡 3) (𝓡 3) id p v)
        (mfderiv (𝓡 3) (𝓡 3) id p w)
    rw [mfderiv_id]
    rfl

end PoincareConjecture.SphereLineProductData
