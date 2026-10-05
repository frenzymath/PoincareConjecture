import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.PeriodicLipschitz
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.AnnulusCollars
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# A genuine locally Lipschitz periodic lift of an admissible annulus

The radial coordinate is clamped to the closed interval and the angular
coordinate is normalized to period one. Convex gluing proves local
Riemannian Lipschitz control across every periodic seam.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff ENNReal NNReal Bundle

namespace PoincareMT.M64Uniformization

local notation "Cover" => ℝ × ℝ

/-- The annular lift scales the angular coordinate by the curve period and clamps its radial
coordinate to the closed unit interval. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-actual-free-modulus-approximation.md`. -/
def scalarAnnulusClamp (z : Cover) : LoopPlane :=
  annulusPoint (curvePeriod * z.1) (projIcc 0 1 (by norm_num) z.2)

private def angularScale : Cover →L[ℝ] LoopPlane :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
      (curvePeriod • EuclideanSpace.basisFun (Fin 2) ℝ 0) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (EuclideanSpace.basisFun (Fin 2) ℝ 1)

private theorem angularScale_apply (z : Cover) :
    angularScale z = annulusPoint (curvePeriod * z.1) z.2 := by
  ext i
  fin_cases i <;> simp [angularScale, annulusPoint, EuclideanSpace.basisFun_apply, mul_comm]

/-- The literal linear angular scaling and radial clamp have a finite global Lipschitz
constant. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit project
construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-actual-free-modulus-approximation.md`. -/
theorem scalarAnnulusClamp_lipschitz :
    ∃ L : ℝ≥0, LipschitzWith L scalarAnnulusClamp := by
  have hclamp : LipschitzWith 1
      (fun z : Cover => (z.1, (projIcc 0 1 (by norm_num) z.2 : ℝ))) := by
    simpa only [max_self, mul_one, Function.comp_def] using!
      LipschitzWith.prod_fst.prodMk
        (((LipschitzWith.subtype_val (Icc (0 : ℝ) 1)).comp
          (LipschitzWith.projIcc (by norm_num : (0 : ℝ) ≤ 1))).comp
            (LipschitzWith.prod_snd : LipschitzWith 1 (@Prod.snd ℝ ℝ)))
  refine ⟨‖angularScale‖₊, ?_⟩
  simpa only [mul_one, Function.comp_def, angularScale_apply, scalarAnnulusClamp] using!
    angularScale.lipschitz.comp hclamp

/-- The clamped lift maps one closed angular fundamental interval into the actual annulus
rectangle. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the explicit project
construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-actual-free-modulus-approximation.md`. -/
theorem scalarAnnulusClamp_mem {z : Cover} (hz : z.1 ∈ Icc (0 : ℝ) 1) :
    scalarAnnulusClamp z ∈ m64AnnulusDomain := by
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hc := (projIcc 0 1 (by norm_num) z.2).property
  change 0 ≤ curvePeriod * z.1 ∧ curvePeriod * z.1 ≤ curvePeriod ∧
    0 ≤ (projIcc 0 1 (by norm_num) z.2 : ℝ) ∧ (projIcc 0 1 (by norm_num) z.2 : ℝ) ≤ 1
  exact ⟨mul_nonneg hP.le hz.1, by nlinarith [hz.2], hc⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The admissible annulus gives a continuous and locally metric-Lipschitz clamped lift,
including every periodic seam. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the
explicit project construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-actual-free-modulus-approximation.md`. -/
theorem scalarAnnulus_clamped_lift
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1) :
    Continuous (A.map ∘ scalarAnnulusClamp) ∧
      ∀ z : Cover, ∃ L : ℝ≥0, ∃ V ∈ 𝓝 z, ∀ x ∈ V, ∀ y ∈ V,
        g.edist (A.map (scalarAnnulusClamp x)) (A.map (scalarAnnulusClamp y)) ≤
          (L : ℝ≥0∞) * edist x y := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : R1Space M := T2Space.r1Space
  let : RegularSpace M := RegularSpace.of_hasBasis
    isCompact_isClosed_basis_nhds (fun _ _ ⟨_, _, h⟩ => h)
  let : T3Space M := ⟨⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hA : LipschitzOnWith
      ⟨A.lipschitz_constant, A.lipschitz_nonnegative⟩ A.map m64AnnulusDomain := by
    intro x hx y hy
    change g.edist (A.map x) (A.map y) ≤ _
    simpa only [ENNReal.coe_nnreal_eq, NNReal.coe_mk, edist_dist, dist_eq_norm] using!
      A.lipschitz_on_domain ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨L, hL⟩ := scalarAnnulusClamp_lipschitz
  have hcomp := hA.comp hL.lipschitzOnWith (fun _ hz => scalarAnnulusClamp_mem hz)
  have hlocal : LocallyLipschitz (A.map ∘ scalarAnnulusClamp) := by
    apply scalar_periodic_strip_locallyLipschitz _ hcomp
    intro x s
    change A.map (annulusPoint (curvePeriod * (x + 1)) _) =
      A.map (annulusPoint (curvePeriod * x) _)
    rw [mul_add, mul_one, A.periodic]
  exact ⟨hlocal.continuous, fun z => hlocal z⟩

end PoincareMT.M64Uniformization
