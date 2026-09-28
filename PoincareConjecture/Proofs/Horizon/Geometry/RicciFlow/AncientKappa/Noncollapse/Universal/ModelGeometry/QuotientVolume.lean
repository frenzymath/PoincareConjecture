import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Involution.Formula
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.PullbackGeodesics
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.LocalIsometry









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

namespace SphereLineProductData

variable {P : Type u} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) P] [IsManifold (𝓡 3) ∞ P]

theorem sphere_edist_le_product_edist (S : SphereLineProductData (P := P)) :
    letI := S.surface_topology
    letI := S.surface_charted
    letI := S.surface_manifold
    letI := S.product_charted
    letI := S.product_manifold
    ∀ x y : S.surface × ℝ,
      edist (S.surface_sphere x.1 : EuclideanSpace ℝ (Fin 3))
        (S.surface_sphere y.1 : EuclideanSpace ℝ (Fin 3)) ≤
          (S.product_metric (-1)).edist x y := by
  let := S.surface_topology
  let := S.surface_charted
  let := S.surface_manifold
  let := S.product_charted
  let := S.product_manifold
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let f : S.surface → EuclideanSpace ℝ (Fin 3) := fun x => (S.surface_sphere x).1
  have hcoe : ContMDiff (𝓡 2) (𝓡 3) ∞
      ((↑) : UnitTwoSphere → EuclideanSpace ℝ (Fin 3)) := contMDiff_coe_sphere
  have hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f :=
    hcoe.comp S.surface_sphere.contMDiff
  have hp : ContMDiff (𝓡 3) (𝓡 2) ∞ (Prod.fst : S.surface × ℝ → S.surface) :=
    contMDiff_fst.comp S.product_smooth_to_canonical
  have hF := hf.comp hp
  have hderiv (x : S.surface × ℝ) (v : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) (f ∘ Prod.fst) x v =
        mfderiv (𝓡 2) (𝓡 3) f x.1 (S.tangent_surface_component x v) := by
    rw [mfderiv_comp_apply x (hf.mdifferentiable (by simp) x.1)
      (hp.mdifferentiable (by simp) x), S.tangent_surface_component_eq]
  intro x y
  have h := (S.product_metric (-1)).edist_le_mul_of_inner_mfderiv_le
    (RiemannianMetric.euclideanMetric 3) (hF.of_le (by simp)) (by norm_num : (0 : ℝ) < 1)
    (fun z v => ?_) x y
  · simpa only [RiemannianMetric.euclideanMetric_edist, ENNReal.ofReal_one,
      one_mul, Function.comp_apply] using h
  · rw [RiemannianMetric.euclideanMetric_inner, hderiv,
      S.product_inner_formula (-1) (by norm_num),
      S.surface_inner_round (-1) (by norm_num)]
    dsimp only [f]
    nlinarith [real_inner_self_nonneg (x := mfderiv (𝓡 2) (𝓡 3)
      (fun x : S.surface => (S.surface_sphere x).1) z.1
      (S.tangent_surface_component z v)), sq_nonneg (S.tangent_line_component z v)]

end SphereLineProductData

namespace QuotientSphereLineCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}

theorem quotient_map_injOn_small_ball (q : QuotientSphereLineCertificate G) :
    letI := q.cover_topology
    letI := q.cover_charted
    letI := q.cover_manifold
    letI := q.product.surface_topology
    letI := q.product.surface_charted
    letI := q.product.surface_manifold
    letI := q.product.product_charted
    letI := q.product.product_manifold
    ∀ p : q.product.surface × ℝ,
      InjOn q.quotient_map ((q.product.product_metric (-1)).ball p (1 / 4)) := by
  let := q.cover_topology
  let := q.cover_charted
  let := q.cover_manifold
  let := q.product.surface_topology
  let := q.product.surface_charted
  let := q.product.surface_manifold
  let := q.product.product_charted
  let := q.product.product_manifold
  have hanti (z : q.product.surface × ℝ) :
      q.product.surface_sphere (q.involution z).1 = -(q.product.surface_sphere z.1) := by
    rcases q.involution_eq_antipodal_identity_or_reflection with h | ⟨c, h⟩
    · simp only [h, q.product.surface_sphere.apply_symm_apply]
    · simp only [h, q.product.surface_sphere.apply_symm_apply]
  intro p x hx y hy hxy
  rcases (q.quotient_fiber_eq_orbit x y).mp hxy with heq | heq
  · exact heq.symm
  have hsmall (z : q.product.surface × ℝ)
      (hz : z ∈ (q.product.product_metric (-1)).ball p (1 / 4)) :
      dist (q.product.surface_sphere p.1 : EuclideanSpace ℝ (Fin 3))
        (q.product.surface_sphere z.1 : EuclideanSpace ℝ (Fin 3)) < 1 / 4 := by
    apply (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 4)).mp
    rw [← edist_dist]
    exact (q.product.sphere_edist_le_product_edist p z).trans_lt hz
  have hx' := hsmall x hx
  have hy' := hsmall y hy
  have hclose : dist (q.product.surface_sphere x.1 : EuclideanSpace ℝ (Fin 3))
      (q.product.surface_sphere y.1 : EuclideanSpace ℝ (Fin 3)) < 1 / 2 := by
    have htriangle := dist_triangle
      (q.product.surface_sphere x.1 : EuclideanSpace ℝ (Fin 3))
      (q.product.surface_sphere p.1 : EuclideanSpace ℝ (Fin 3))
      (q.product.surface_sphere y.1 : EuclideanSpace ℝ (Fin 3))
    rw [dist_comm (q.product.surface_sphere x.1 : EuclideanSpace ℝ (Fin 3))
      (q.product.surface_sphere p.1 : EuclideanSpace ℝ (Fin 3))] at htriangle
    linarith
  have hnorm : ‖(q.product.surface_sphere x.1 : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      (q.product.surface_sphere x.1).property
  have hdist : dist (q.product.surface_sphere x.1 : EuclideanSpace ℝ (Fin 3))
      (q.product.surface_sphere y.1 : EuclideanSpace ℝ (Fin 3)) = 2 := by
    rw [heq, hanti]
    change ‖(q.product.surface_sphere x.1 : EuclideanSpace ℝ (Fin 3)) -
      -(q.product.surface_sphere x.1 : EuclideanSpace ℝ (Fin 3))‖ = 2
    rw [sub_neg_eq_add, ← two_smul ℝ, norm_smul, Real.norm_two, hnorm]
    norm_num
  linarith

section Volume

variable (q : QuotientSphereLineCertificate G)

local instance : TopologicalSpace q.cover := q.cover_topology
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) q.cover := q.cover_charted
local instance : IsManifold (𝓡 3) ∞ q.cover := q.cover_manifold
local instance : TopologicalSpace q.product.surface := q.product.surface_topology
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 2)) q.product.surface :=
  q.product.surface_charted
local instance : IsManifold (𝓡 2) ∞ q.product.surface := q.product.surface_manifold
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (q.product.surface × ℝ) :=
  q.product.product_charted
local instance : IsManifold (𝓡 3) ∞ (q.product.surface × ℝ) := q.product.product_manifold
local instance : TopologicalSpace q.quotient_carrier := q.quotient_topology
local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) q.quotient_carrier := q.quotient_charted
local instance : IsManifold (𝓡 3) ∞ q.quotient_carrier := q.quotient_manifold
local instance : T3Space q.product.surface :=
  q.product.surface_sphere.toHomeomorph.isEmbedding.t3Space
local instance : SecondCountableTopology q.product.surface :=
  q.product.surface_sphere.toHomeomorph.isEmbedding.secondCountableTopology
local instance : T3Space q.quotient_carrier :=
  (Classical.choose q.flow_isometric_to_quotient).toHomeomorph.t3Space

variable [MeasurableSpace (q.product.surface × ℝ)] [BorelSpace (q.product.surface × ℝ)]
  [MeasurableSpace q.quotient_carrier] [BorelSpace q.quotient_carrier]

theorem product_ball_volume_le_quotient_ball_volume (p : q.product.surface × ℝ) :
    (q.product.product_metric (-1)).volumeMeasure
        ((q.product.product_metric (-1)).ball p (1 / 4)) ≤
      (q.quotient_metric (-1)).volumeMeasure
        ((q.quotient_metric (-1)).ball (q.quotient_map p) (1 / 4)) := by
  exact (q.product.product_metric (-1)).volumeMeasure_ball_le_of_injOn_metric_pullback
    (q.quotient_metric (-1)) q.quotient_map_smooth
    (q.quotient_metric_pullback (-1) (by norm_num)) p (1 / 4)
    (q.quotient_map_injOn_small_ball p)

end Volume

end QuotientSphereLineCertificate
end PoincareConjecture
