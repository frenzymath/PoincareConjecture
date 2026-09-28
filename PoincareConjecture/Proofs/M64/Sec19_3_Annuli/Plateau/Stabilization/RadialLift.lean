import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FiberMetric
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.LipschitzAnnulusAdapter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Bundle
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

def auxiliaryCircleRadialLift (P : M62.CircleProductData F circumference)
    (f : LoopPlane → M) (delta : ℝ) : LoopPlane → P.charts.Point :=
  fun z => (f z, P.circle.quotient (delta * z 1))

theorem auxiliaryCircle_radial_lipschitz
    (P : M62.CircleProductData F circumference) (time : ℝ)
    {c0 c1 : ℝ → M} (A : M64Annulus (F.metric time) c0 c1) (delta : ℝ)
    (x y : m64AnnulusDomain) :
    (P.flow.metric time).edist (auxiliaryCircleRadialLift P A.map delta x)
        (auxiliaryCircleRadialLift P A.map delta y) ≤
      ENNReal.ofReal (A.lipschitz_constant + |delta|) *
        ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
  have hcoord : |(x : LoopPlane) 1 - (y : LoopPlane) 1| ≤ ‖(x : LoopPlane) - y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
      PiLp.norm_apply_le ((x : LoopPlane) - (y : LoopPlane)) (1 : Fin 2)
  have haux : ENNReal.ofReal |delta * (x : LoopPlane) 1 - delta * (y : LoopPlane) 1| ≤
      ENNReal.ofReal |delta| * ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
    rw [← mul_sub, abs_mul, ENNReal.ofReal_mul (abs_nonneg delta)]
    gcongr
  calc
    (P.flow.metric time).edist (auxiliaryCircleRadialLift P A.map delta x)
        (auxiliaryCircleRadialLift P A.map delta y) ≤
        (F.metric time).edist (A.map x) (A.map y) +
          ENNReal.ofReal |delta * (x : LoopPlane) 1 - delta * (y : LoopPlane) 1| :=
      auxiliaryCircle_product_edist_le P time _ _ _ _
    _ ≤ ENNReal.ofReal A.lipschitz_constant * ENNReal.ofReal ‖(x : LoopPlane) - y‖ +
        ENNReal.ofReal |delta| * ENNReal.ofReal ‖(x : LoopPlane) - y‖ :=
      add_le_add (A.lipschitz_on_domain x y) haux
    _ = ENNReal.ofReal (A.lipschitz_constant + |delta|) *
        ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
      rw [ENNReal.ofReal_add A.lipschitz_nonnegative (abs_nonneg delta), add_mul]

theorem auxiliaryCircle_radial_annulus [T2Space M]
    (P : M62.CircleProductData F circumference) (time : ℝ)
    {c0 c1 : ℝ → M} (A : M64Annulus (F.metric time) c0 c1) (delta : ℝ) :
    ∃ B : M64Annulus (P.flow.metric time)
      (auxiliaryCircleSection P (P.circle.quotient 0) ∘ c0)
      (auxiliaryCircleSection P (P.circle.quotient delta) ∘ c1),
      B.map = auxiliaryCircleRadialLift P A.map delta := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let := P.circle.chartedSpace
  have hcont : Continuous (fun z : LoopPlane => P.circle.quotient (delta * z 1)) := by
    exact P.circle.quotient_smooth.continuous.comp (by fun_prop)
  have hfinite : volume m64AnnulusInterior ≠ (⊤ : ENNReal) := by
    rw [← measure_congr m64AnnulusDomain_ae_eq_interior]
    exact m64AnnulusDomain_volume_ne_top
  obtain ⟨B, hB, -⟩ := m64Annulus_of_lipschitz (P.flow.metric time)
    (c0 := auxiliaryCircleSection P (P.circle.quotient 0) ∘ c0)
    (c1 := auxiliaryCircleSection P (P.circle.quotient delta) ∘ c1)
    (auxiliaryCircleRadialLift P A.map delta)
    (A.continuous_on_domain.prodMk hcont.continuousOn)
    (fun x s => by
      change (A.map (annulusPoint (x + curvePeriod) s), P.circle.quotient (delta * s)) =
        (A.map (annulusPoint x s), P.circle.quotient (delta * s))
      rw [A.periodic])
    (fun x => by
      change (A.map (annulusPoint x 0), P.circle.quotient (delta * 0)) =
        (c0 x, P.circle.quotient 0)
      rw [A.lower_boundary, mul_zero])
    (fun x => by
      change (A.map (annulusPoint x 1), P.circle.quotient (delta * 1)) =
        (c1 x, P.circle.quotient delta)
      rw [A.upper_boundary, mul_one])
    (add_nonneg A.lipschitz_nonnegative (abs_nonneg delta))
    (auxiliaryCircle_radial_lipschitz P time A delta) hfinite
    (lt_add_one (∫ z in m64AnnulusDomain,
      m60AreaDensity (P.flow.metric time) (auxiliaryCircleRadialLift P A.map delta) z))
  exact ⟨B, hB⟩

theorem auxiliaryCircle_separated_boundary_ranges
    (P : M62.CircleProductData F circumference) (c0 c1 : ℝ → M)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta < circumference) :
    Disjoint (range (auxiliaryCircleSection P (P.circle.quotient 0) ∘ c0))
      (range (auxiliaryCircleSection P (P.circle.quotient delta) ∘ c1)) := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hxy⟩
  have hq := congrArg Prod.snd hxy
  have hz : (delta : AddCircle circumference) = 0 := hq
  exact hdelta.ne' ((AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hdelta.le, hsmall⟩).mp hz)

end PoincareConjecture.M64
