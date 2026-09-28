import PoincareConjecture.Proofs.M35.CapGeometry.ReflectedDeckField
import PoincareConjecture.Proofs.M35.CapGeometry.M27ProductChartMetric
import PoincareConjecture.Proofs.M35.CapGeometry.RoundProductParallel









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)
local notation "Ip" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)



theorem cylinderChart_pullback_axial (q : UnitTwoSphere)
    (Y : (p : UnitTwoSphere × ℝ) → TangentSpace Ip p) (x : V) :
    (cylinderCoordinateEquiv (mpullback (𝓡 3) Ip (cylinderChart q) Y x)).2 =
      (Y (cylinderChart q x)).2 := by
  have h := (cylinderChart_mfderiv_invertible q x).self_apply_inverse (Y (cylinderChart q x))
  have hs := congrArg (fun v : TangentSpace Ip (cylinderChart q x) => v.2) h
  simpa only [mfderiv_cylinderChart, mpullback] using! hs

variable {M : Type*} [TopologicalSpace M] [ChartedSpace V M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}


noncomputable def twistedChartLift (N : M27TwistedSphereLineFlowCertificate K)
    (q : UnitTwoSphere) (Z : (p : M) → TangentSpace (𝓡 3) p) : V → V :=
  mpullback (𝓡 3) Ip (cylinderChart q) (mpullback Ip (𝓡 3) N.cover Z)


theorem twistedChartLift_axial_odd (N : M27TwistedSphereLineFlowCertificate K)
    (q : UnitTwoSphere) (Z : (p : M) → TangentSpace (𝓡 3) p) {x y : V}
    (hpoints : cylinderChart q y = m27TwistedProductInvolution (cylinderChart q x)) :
    (cylinderCoordinateEquiv (twistedChartLift N q Z y)).2 =
      -(cylinderCoordinateEquiv (twistedChartLift N q Z x)).2 := by
  let Y := mpullback Ip (𝓡 3) N.cover Z
  calc
    _ = (Y (cylinderChart q y)).2 := cylinderChart_pullback_axial q Y y
    _ = (Y (m27TwistedProductInvolution (cylinderChart q x))).2 :=
      congrArg (fun p : UnitTwoSphere × ℝ => (Y p).2) hpoints
    _ = -(Y (cylinderChart q x)).2 := twisted_cover_field_axial_odd N Z _
    _ = _ := congrArg (fun r : ℝ => -r) (cylinderChart_pullback_axial q Y x).symm



theorem twistedChartLift_limit_axial_odd (N : M27TwistedSphereLineFlowCertificate K)
    (q : UnitTwoSphere) (Zseq : ℕ → (p : M) → TangentSpace (𝓡 3) p)
    {Z : V → V} {x y : V}
    (hpoints : cylinderChart q y = m27TwistedProductInvolution (cylinderChart q x))
    (hx : Tendsto (fun k => twistedChartLift N q (Zseq k) x) atTop (𝓝 (Z x)))
    (hy : Tendsto (fun k => twistedChartLift N q (Zseq k) y) atTop (𝓝 (Z y))) :
    (cylinderCoordinateEquiv (Z y)).2 = -(cylinderCoordinateEquiv (Z x)).2 := by
  have hc : Continuous (fun v : V => (cylinderCoordinateEquiv v).2) :=
    continuous_snd.comp cylinderCoordinateEquiv.continuous
  have hxx := (hc.tendsto _).comp hx
  have hyy := (hc.tendsto _).comp hy
  have he : (fun k => -(cylinderCoordinateEquiv (twistedChartLift N q (Zseq k) x)).2)
      =ᶠ[atTop] (fun k => (cylinderCoordinateEquiv (twistedChartLift N q (Zseq k) y)).2) :=
    Eventually.of_forall fun k => (twistedChartLift_axial_odd N q (Zseq k) hpoints).symm
  exact tendsto_nhds_unique hyy (hxx.neg.congr' he)



theorem twistedChartLift_parallel_limit_false
    (N : M27TwistedSphereLineFlowCertificate K) (q : UnitTwoSphere)
    (Zseq : ℕ → (p : M) → TangentSpace (𝓡 3) p)
    {Ω : Set V} (hΩ : IsOpen Ω) (hconnected : IsPreconnected Ω)
    {Z : V → V} (hZ : ContDiffOn ℝ ∞ Z Ω)
    (hparallel : ∀ x ∈ Ω, ∀ v : V, (twistedProductChartConnection N 0 q).connection Z x v = 0)
    {x y : V} (hxΩ : x ∈ Ω) (hyΩ : y ∈ Ω)
    (hunit : (twistedProductChartMetric N 0 q).inner x (Z x) (Z x) = 1)
    (hpoints : cylinderChart q y = m27TwistedProductInvolution (cylinderChart q x))
    (hx : Tendsto (fun k => twistedChartLift N q (Zseq k) x) atTop (𝓝 (Z x)))
    (hy : Tendsto (fun k => twistedChartLift N q (Zseq k) y) atTop (𝓝 (Z y))) : False := by
  obtain ⟨c, hc, hround⟩ := m27SphereChartMetric_round N.sphere 0 le_rfl q
  exact product_parallel_reflection_false (twistedProductChartConnection N 0 q)
    (m27SphereChartConnection N.sphere 0 q) hΩ hconnected
    (fun x _ => twistedProductChartMetric_product N 0 le_rfl q x) hZ hparallel hxΩ hyΩ hunit
    (fun u v hu hv huv => (hround _ u v hu hv huv).symm ▸ hc)
    (twistedChartLift_limit_axial_odd N q Zseq hpoints hx hy)

end PoincareConjecture.M35
