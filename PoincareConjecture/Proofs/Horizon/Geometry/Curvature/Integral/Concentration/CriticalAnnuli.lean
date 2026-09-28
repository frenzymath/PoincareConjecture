import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.AscentRestriction
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.ScaleScalarAnnuli












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

universe u

namespace Poincare.CurvatureIntegral



theorem hasLocalDistanceAscent_on_annulus_of_two_mul_badAscentRadius_le
    {X : Type*} [MetricSpace X] {p : X} {c c' b r r₀ : ℝ}
    (hcc' : c' ≤ c) (hinner : 2 * badAscentRadius c b p ≤ r)
    (hr : r ≤ r₀) (houter : 3 * r₀ ≤ b) :
    ∀ y : X, r / 2 < dist p y → dist p y < 3 * r →
      HasLocalDistanceAscent c' p y := by
  intro y hylo hyhi
  apply HasLocalDistanceAscent.mono
    (hasLocalDistanceAscent_of_badAscentRadius_lt
      (by linarith : badAscentRadius c b p < dist p y)
      (by linarith : dist p y ≤ b)) hcc'

end Poincare.CurvatureIntegral

namespace PoincareConjecture.RiemannianMetric

open Poincare.CurvatureIntegral



theorem exists_radial_annulus_scalar_bound_above_badAscentRadius
    {m : ℕ} (hm : 1 ≤ m) {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    [IsManifold (𝓡 (m + 2)) ∞ M]
    (g : RiemannianMetric (m + 2) M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hsec : ∀ x : M, ∀ v w : TangentSpace (𝓡 (m + 2)) x,
      -1 ≤ D.sectionalCurvature x v w)
    (p : M) {c b₀ r₀ : ℝ} (hcrate : (1 : ℝ) / 2 ≤ c)
    (_hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hcap : 3 * r₀ ≤ b₀) :
    letI := g.toMetricSpace
    ∀ r : ℝ, 0 < r → r ≤ r₀ → 2 * badAscentRadius c b₀ p ≤ r →
      let a := 7 * r / 12
      let b := 3 * r / 5
      let α := scaleAnnularInductionConstant m
      let I := Ioo (9 * r / 16) (15 * r / 16)
      ∃ (f : M → ℝ) (hf : ContMDiff (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ f),
        IsProperMap (I.restrictPreimage f) ∧ Icc a (3 * b / 2) ⊆ I ∧
        (∀ x : M, f x ∈ I → mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) f x ≠ 0) ∧
        f ⁻¹' Icc a (3 * b / 2) ⊆ g.ball p (2 * r) ∧
        {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)} ⊆
          f ⁻¹' Icc a b ∧
        let U := g.regularDomain hf
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 2))) = m + 2) :=
          ⟨finrank_euclideanSpace_fin⟩
        letI (t : ℝ) := openLevelSetChartedSpace hf U (g.regularDomain_regular hf) (m + 1) t
        letI (t : ℝ) := isManifold_openLevelSet hf U (g.regularDomain_regular hf) (m + 1) t
        let DL := fun t => (RiemannianMetric.regularLevelMetric
          hf U (g.regularDomain_regular hf) t g).leviCivitaData
        ∀ C : ℝ, 0 ≤ C →
          (∀ t ∈ Icc a (3 * b / 2),
            (∫ z, max 0 ((DL t).scalarCurvature z)
              ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t) ≤
            C * (r ^ (m - 1) + ∫ z,
              D.levelSectionalError f (fun _ => 1) (α / t) (openLevelIncl f U t z)
              ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) t)) →
          (∫ x in {x : M | (g.edist p x).toReal ∈
              Icc (113 * r / 96) (19 * r / 16)},
            max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
            scaleScalarAnnulusConstant m C * r ^ m := by
  let := g.toMetricSpace
  intro r hr hrr₀ hinner
  have hascent := hasLocalDistanceAscent_on_annulus_of_two_mul_badAscentRadius_le
    hcrate hinner hrr₀ hcap
  exact g.exists_radial_annulus_scalar_bound_with_dimensional_constant
    hm D hc hsec p hr (hrr₀.trans hr₀1) hascent

end PoincareConjecture.RiemannianMetric
