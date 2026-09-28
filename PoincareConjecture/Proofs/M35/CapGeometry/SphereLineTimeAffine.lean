import PoincareConjecture.Proofs.M35.CapGeometry.SphereLineChartTime
import PoincareConjecture.Proofs.M35.CapGeometry.RoundFactorTime

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem sphereLineFactor_hasDerivWithinAt (N : M27SphereLineFlowCertificate K)
    (t : ℝ) (ht : t ≤ 0) (q : UnitTwoSphere) (x u v : E2) :
    HasDerivWithinAt (fun s => (m27SphereChartMetric N.sphere s q).inner x u v)
      (-2 * (m27SphereChartConnection N.sphere t q).ricci x u v) (Iic 0) t := by
  let X := cylinderCoordinateEquiv.symm (x, 0)
  let U := cylinderCoordinateEquiv.symm (u, 0)
  let W := cylinderCoordinateEquiv.symm (v, 0)
  have hd := sphereLineChartMetric_hasDerivWithinAt N t ht q X U W
  rw [product_ricci (sphereLineChartConnection N t q)
    (m27SphereChartConnection N.sphere t q) (sphereLineChartMetric_product N t ht q)] at hd
  let R (a b c : E2) := (m27SphereChartConnection N.sphere t q).ricci a b c
  change HasDerivWithinAt (fun s => (sphereLineChartMetric N s q).inner X U W)
    (-2 * R (cylinderCoordinateEquiv X).1 (cylinderCoordinateEquiv U).1
      (cylinderCoordinateEquiv W).1) (Iic 0) t at hd
  simp only [X, U, W, ContinuousLinearEquiv.apply_symm_apply] at hd
  apply hd.congr_of_mem ?_ ht
  intro s hs
  rw [sphereLineChartMetric_product N s hs q]
  simp only [ContinuousLinearEquiv.apply_symm_apply, zero_mul, add_zero]
  let G (a b c : E2) := (m27SphereChartMetric N.sphere s q).inner a b c
  change G x u v = G (cylinderCoordinateEquiv (cylinderCoordinateEquiv.symm (x, 0))).1 u v
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem sphereLineChartMetric_time_affine (N : M27SphereLineFlowCertificate K)
    (t : ℝ) (ht : t ≤ 0) (q : UnitTwoSphere) (x u v : V) :
    (sphereLineChartMetric N t q).inner x u v =
      (sphereLineChartMetric N 0 q).inner x u v -
        2 * t * (sphereLineChartConnection N 0 q).ricci x u v := by
  rw [sphereLineChartMetric_product N t ht q,
    sphereLineChartMetric_product N 0 le_rfl q,
    product_ricci (sphereLineChartConnection N 0 q)
      (m27SphereChartConnection N.sphere 0 q) (sphereLineChartMetric_product N 0 le_rfl q),
    round_factor_metric_time_affine (fun s => m27SphereChartMetric N.sphere s q)
      (fun s => m27SphereChartConnection N.sphere s q)
      (fun s hs => m27SphereChartMetric_round N.sphere s hs q)
      (fun s hs => sphereLineFactor_hasDerivWithinAt N s hs q) t ht]
  ring

theorem sphereLineChartMetric_two_times (N : M27SphereLineFlowCertificate K)
    (t : ℝ) (ht : t ≤ 0) (tau : ℝ) (htau : 0 < tau)
    (q : UnitTwoSphere) (x u v : V) :
    (sphereLineChartMetric N t q).inner x u v =
      (1 + t / tau) * (sphereLineChartMetric N 0 q).inner x u v -
        (t / tau) * (sphereLineChartMetric N (-tau) q).inner x u v := by
  rw [sphereLineChartMetric_time_affine N t ht,
    sphereLineChartMetric_time_affine N (-tau) (neg_nonpos.mpr htau.le)]
  field_simp [htau.ne']
  ring

theorem sphereLine_metric_two_times (N : M27SphereLineFlowCertificate K)
    (t : ℝ) (ht : t ≤ 0) (tau : ℝ) (htau : 0 < tau)
    (p : M) (u v : TangentSpace (𝓡 3) p) :
    (K.flow.metric t).inner p u v =
      (1 + t / tau) * (K.flow.metric 0).inner p u v -
        (t / tau) * (K.flow.metric (-tau)).inner p u v := by
  let c := N.identification.symm p
  let q := c.1
  let X := cylinderCoordinateEquiv.symm ((chartAt E2 q) q, c.2)
  have hchart : cylinderChart q X = c := by
    apply Prod.ext
    · change (chartAt E2 q).symm (cylinderCoordinateEquiv X).1 = c.1
      dsimp only [X]
      rw [ContinuousLinearEquiv.apply_symm_apply]
      exact (chartAt E2 q).left_inv (mem_chart_source E2 q)
    · change (cylinderCoordinateEquiv X).2 = c.2
      simp only [X, ContinuousLinearEquiv.apply_symm_apply]
  have hp : N.identification (cylinderChart q X) = p := by
    rw [hchart]
    exact N.identification.apply_symm_apply p
  obtain ⟨U, hU⟩ := (sphereLineChart_invertible N q X).surjective u
  obtain ⟨W, hW⟩ := (sphereLineChart_invertible N q X).surjective v
  have h := sphereLineChartMetric_two_times N t ht tau htau q X U W
  change (K.flow.metric t).inner (N.identification (cylinderChart q X))
    (mfderiv (𝓡 3) (𝓡 3) (N.identification ∘ cylinderChart q) X U)
    (mfderiv (𝓡 3) (𝓡 3) (N.identification ∘ cylinderChart q) X W) =
      (1 + t / tau) * (K.flow.metric 0).inner (N.identification (cylinderChart q X))
        (mfderiv (𝓡 3) (𝓡 3) (N.identification ∘ cylinderChart q) X U)
        (mfderiv (𝓡 3) (𝓡 3) (N.identification ∘ cylinderChart q) X W) -
      (t / tau) * (K.flow.metric (-tau)).inner (N.identification (cylinderChart q X))
        (mfderiv (𝓡 3) (𝓡 3) (N.identification ∘ cylinderChart q) X U)
        (mfderiv (𝓡 3) (𝓡 3) (N.identification ∘ cylinderChart q) X W) at h
  rw [hU, hW] at h
  let tensor (s : ℝ) (y : M) (a b : V) := (K.flow.metric s).inner y a b
  change tensor t (N.identification (cylinderChart q X)) u v =
    (1 + t / tau) * tensor 0 (N.identification (cylinderChart q X)) u v -
      (t / tau) * tensor (-tau) (N.identification (cylinderChart q X)) u v at h
  rw [hp] at h
  exact h

end PoincareConjecture.M35
