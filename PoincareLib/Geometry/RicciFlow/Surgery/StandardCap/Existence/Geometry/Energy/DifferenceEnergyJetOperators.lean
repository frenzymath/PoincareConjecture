import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.CurvatureJetRealization
import PoincareLib.Geometry.RicciFlow.Local.Connection.NativeTime
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Connection.NativeTime
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Connection.Variation
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureHom
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvaturePairExchange
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureRicciSecondDerivative
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureTrace
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Calculus.CurvatureTrilinear
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Curvature.Energy.CurvatureRateAlgebra
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Coefficients.CompactFiniteCoefficient
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Comparison.RateFiniteAlgebra
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Comparison.ScalarEnergyComparison
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Energy.Coordinates.FamilyBundleCoordinates
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Metric.MetricCompactBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Metric.MetricDifferenceEvolution
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.Local.Metric.MetricInverse

/-!
# Finite metric jets for the difference-energy background coefficients

Inverse metrics, Christoffel symbols, raised curvature, and its ordinary
spatial derivative are universal smooth functions of three metric jets.
The raised tensor is obtained by the actual inverse metric, respecting the
book's last-slot convention. Compact elliptic jet boxes give one bound before
any metric, point, or translated chart is chosen.
This is the coefficient preparation for Morgan-Tian Section 12.5,
pp. 309-319; see uniform-difference-energy-coefficients.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The finite metric jets have dependent products of multilinear-map targets.
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareMT.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

/-- Raise the third slot of the book's four-covariant curvature formula
using the formal zeroth metric coefficient (Section 12.5, pp. 309-319). -/
noncomputable def raisedCurvatureTwoJet {n : ℕ} (J : MetricTwoJet n)
    (u v w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  J.1.inverse (∑ i : Fin n,
    (jetCurvature J u v (EuclideanSpace.single i 1) w) • EuclideanSpace.proj i)

/-- The raised curvature readout is smooth wherever the formal metric
coefficient is invertible (Section 12.5, pp. 309-319). -/
theorem contDiffAt_raisedCurvatureTwoJet {n : ℕ} {J : MetricTwoJet n}
    (hJ : J.1.IsInvertible) (u v w : EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ ∞ (fun K => raisedCurvatureTwoJet K u v w) J := by
  have hI : ContDiffAt ℝ ∞ (fun K : MetricTwoJet n => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  apply hI.clm_apply
  apply ContDiffAt.sum
  intro i _
  exact (contDiffAt_jetCurvature hJ _ _ _ _).smul contDiffAt_const

/-- The inverse metric entries as a function of a formal two-jet
(Section 12.5, pp. 309-319). -/
noncomputable def inverseMetricJetArray (n : ℕ)
    (J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 2)
    (i j : Fin n) : ℝ :=
  EuclideanSpace.proj i ((twoJetProjection n J).1.inverse (EuclideanSpace.proj j))

/-- The connection entries, with direction first, section second, and
output third, as a function of the metric jet (Section 12.5, pp. 309-319). -/
noncomputable def connectionJetArray (n : ℕ)
    (J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 2)
    (i j l : Fin n) : ℝ :=
  EuclideanSpace.proj l (jetChristoffel (twoJetProjection n J)
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))

/-- The raised curvature entries, with output first and the three
curvature inputs following, on formal metric jets
(Section 12.5, pp. 309-319). -/
noncomputable def raisedCurvatureJetArray (n : ℕ)
    (J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 2)
    (l j k m : Fin n) : ℝ :=
  EuclideanSpace.proj l (raisedCurvatureTwoJet (twoJetProjection n J)
    (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) (EuclideanSpace.single m 1))

/-- Inverse entries are jointly smooth on the invertible jet domain
(Section 12.5, pp. 309-319). -/
theorem contDiffOn_inverseMetricJetArray (n : ℕ) :
    ContDiffOn ℝ ∞ (inverseMetricJetArray n) (jetRicciFlowDomain n) := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j J hJ
  have hI : ContDiffAt ℝ ∞
      (fun K : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 2 =>
        (twoJetProjection n K).1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J
      (contDiffAt_fst.comp J (twoJetProjection n).contDiff.contDiffAt)
  exact ((EuclideanSpace.proj i).contDiff.contDiffAt.comp J
    (hI.clm_apply contDiffAt_const)).contDiffWithinAt

/-- The connection array is smooth on the actual invertible metric
jet domain (Section 12.5, pp. 309-319). -/
theorem contDiffOn_connectionJetArray (n : ℕ) :
    ContDiffOn ℝ ∞ (connectionJetArray n) (jetRicciFlowDomain n) := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  apply contDiffOn_pi.mpr
  intro l J hJ
  have hΓ := (contDiffAt_jetChristoffel hJ
    (u := fun _ => EuclideanSpace.single i 1)
    (v := fun _ => EuclideanSpace.single j 1) contDiffAt_const contDiffAt_const).comp J
      (twoJetProjection n).contDiff.contDiffAt
  exact ((EuclideanSpace.proj l).contDiff.contDiffAt.comp J hΓ).contDiffWithinAt

/-- The raised curvature array is smooth on the actual invertible
metric jet domain (Section 12.5, pp. 309-319). -/
theorem contDiffOn_raisedCurvatureJetArray (n : ℕ) :
    ContDiffOn ℝ ∞ (raisedCurvatureJetArray n) (jetRicciFlowDomain n) := by
  apply contDiffOn_pi.mpr
  intro l
  apply contDiffOn_pi.mpr
  intro j
  apply contDiffOn_pi.mpr
  intro k
  apply contDiffOn_pi.mpr
  intro m J hJ
  have hR := (contDiffAt_raisedCurvatureTwoJet hJ
    (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)
    (EuclideanSpace.single m 1)).comp J (twoJetProjection n).contDiff.contDiffAt
  exact ((EuclideanSpace.proj l).contDiff.contDiffAt.comp J hR).contDiffWithinAt

/-- The complete finite-dimensional background needed by the local
difference-energy coefficients: inverse, connection, raised curvature,
and ordinary spatial curvature derivative (Section 12.5, pp. 309-319). -/
noncomputable def differenceEnergyJetBackground (n : ℕ)
    (J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 3) :=
  ((inverseMetricJetArray n (truncate 2 J), connectionJetArray n (truncate 2 J)),
    (raisedCurvatureJetArray n (truncate 2 J), prolong 2 (raisedCurvatureJetArray n) J))

/-- The background coefficient readout is smooth on the three-jet
invertible domain, including its ordinary derivative component
(Section 12.5, pp. 309-319). -/
theorem contDiffOn_differenceEnergyJetBackground (n : ℕ) :
    ContDiffOn ℝ ∞ (differenceEnergyJetBackground n) (curvatureJetDomain n 1) := by
  have htr : ContDiffOn ℝ ∞
      (truncate (E := EuclideanSpace ℝ (Fin n)) (V := MetricCoefficient n) 2)
      (curvatureJetDomain n 1) :=
    (truncate (E := EuclideanSpace ℝ (Fin n)) (V := MetricCoefficient n) 2).contDiff.contDiffOn
  have hi := (contDiffOn_inverseMetricJetArray n).comp htr (fun _ h => h)
  have hΓ := (contDiffOn_connectionJetArray n).comp htr (fun _ h => h)
  have hR := (contDiffOn_raisedCurvatureJetArray n).comp htr (fun _ h => h)
  have hdR := contDiffOn_prolong (isOpen_jetRicciFlowDomain n)
    (contDiffOn_raisedCurvatureJetArray n)
  exact (hi.prodMk hΓ).prodMk (hR.prodMk hdR)

/-- A compact elliptic metric-jet box bounds all background entries and
the spatial curvature derivative before any actual geometry is chosen
(Section 12.5, pp. 309-319). -/
theorem differenceEnergyJetBackground_bound (n : ℕ) {a : ℝ} (ha : 0 < a) (H : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 3,
        ‖J‖ ≤ H →
        (∀ v, a * ‖v‖ ^ 2 ≤
          (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin n))
            (MetricCoefficient n) (J 0)) v v) →
        ‖differenceEnergyJetBackground n J‖ ≤ C := by
  obtain ⟨K, hK, hKU, hbox⟩ := exists_compact_elliptic_jet_box n 1 ha H
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((contDiffOn_differenceEnergyJetBackground n).continuousOn.mono hKU)
  exact ⟨max C 1, le_max_right _ _, fun J hJ hell =>
    (hC J (hbox J hJ hell)).trans (le_max_left _ _)⟩

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- The formal raising operation reconstructs the actual retained
one-output curvature tensor with the book's precise slot convention
(Section 12.5, pp. 309-319). -/
theorem raisedCurvatureTwoJet_metricTwoJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x u v w : EuclideanSpace ℝ (Fin n)) :
    raisedCurvatureTwoJet (metricTwoJet g.euclideanCoefficients x) u v w =
      D.curvature x u v w := by
  unfold raisedCurvatureTwoJet
  simp_rw [jetCurvature_metricTwoJet D]
  exact Proofs.M03.inverse_bilinear_reconstruct (g.inner_isInvertible x) _

/-- On actual metric jets the formal connection array is exactly the
retained connection on constant fields (Section 12.5, pp. 309-319). -/
theorem connectionJetArray_spatialJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) (i j l : Fin n) :
    connectionJetArray n (spatialJet 2
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients p.2) (0, x)) i j l =
      EuclideanSpace.proj l
        (D.euclideanConnection (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) x) := by
  simp only [connectionJetArray, twoJetProjection_spatialJet, jetChristoffel_metricTwoJet D]

/-- On actual metric jets the raised array equals the genuine retained
curvature components (Section 12.5, pp. 309-319). -/
theorem raisedCurvatureJetArray_spatialJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) (l j k m : Fin n) :
    raisedCurvatureJetArray n (spatialJet 2
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients p.2) (0, x)) l j k m =
      EuclideanSpace.proj l (D.curvature x (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1) (EuclideanSpace.single m 1)) := by
  simp only [raisedCurvatureJetArray, twoJetProjection_spatialJet,
    raisedCurvatureTwoJet_metricTwoJet D]

/-- Prolonging the raised curvature readout gives the genuine ordinary
spatial derivative of all retained curvature components
(Section 12.5, pp. 309-319). -/
theorem hasFDerivAt_raisedCurvatureJetArray {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun y l j k m => EuclideanSpace.proj l
      (D.curvature y (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1) (EuclideanSpace.single m 1)))
      (prolong 2 (raisedCurvatureJetArray n) (spatialJet 3
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients p.2) (0, x))) x := by
  let f := fun p : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients p.2
  have hmem : spatialJet 2 f (0, x) ∈ jetRicciFlowDomain n :=
    metric_spatialJet_mem_curvatureJetDomain g 0 x
  have hR := (contDiffOn_raisedCurvatureJetArray n).contDiffAt
    ((isOpen_jetRicciFlowDomain n).mem_nhds hmem)
  have hd := (hR.differentiableAt (by simp)).hasFDerivAt.comp x
    (hasFDerivAt_spatialJet 2 f 0 x (g.contDiffAt_euclideanCoefficients x))
  convert! hd using 1
  funext y l j k m
  exact (raisedCurvatureJetArray_spatialJet D y l j k m).symm

/-- The actual inverse, connection, raised curvature, and ordinary
curvature derivative in fixed Euclidean coordinates
(Section 12.5, pp. 309-319). -/
noncomputable def differenceEnergyBackground {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) :=
  ((fun i j : Fin n => EuclideanSpace.proj i
      ((g.euclideanCoefficients x).inverse (EuclideanSpace.proj j)),
    fun i j l : Fin n => EuclideanSpace.proj l
      (D.euclideanConnection (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) x)),
    (fun l j k m : Fin n => EuclideanSpace.proj l
      (D.curvature x (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1) (EuclideanSpace.single m 1)),
      fderiv ℝ (fun y l j k m => EuclideanSpace.proj l
        (D.curvature y (EuclideanSpace.single j 1)
          (EuclideanSpace.single k 1) (EuclideanSpace.single m 1))) x))

/-- All four formal background fields, including the ordinary
derivative, equal the actual retained geometric fields
(Section 12.5, pp. 309-319). -/
theorem differenceEnergyJetBackground_spatialJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) :
    differenceEnergyJetBackground n (spatialJet 3
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients p.2) (0, x)) =
      differenceEnergyBackground D x := by
  apply Prod.ext
  · apply Prod.ext
    · funext i j
      simp only [differenceEnergyJetBackground, differenceEnergyBackground,
        inverseMetricJetArray, truncate_spatialJet, twoJetProjection_spatialJet]
      rfl
    · funext i j l
      exact connectionJetArray_spatialJet D x i j l
  · apply Prod.ext
    · funext l j k m
      exact raisedCurvatureJetArray_spatialJet D x l j k m
    · exact (hasFDerivAt_raisedCurvatureJetArray D x).fderiv.symm

/-- One constant controls the actual coordinate background of every
metric and compatible connection with the specified elliptic three-jet
bound (Section 12.5, pp. 309-319). -/
theorem differenceEnergyBackground_bound_of_metric_jets
    (n : ℕ) {a : ℝ} (ha : 0 < a) (H : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g)
        (x : EuclideanSpace ℝ (Fin n)),
        (∀ j ≤ 3, ‖iteratedFDeriv ℝ j g.euclideanCoefficients x‖ ≤ H) →
        (∀ v, a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v) →
        ‖differenceEnergyBackground D x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := differenceEnergyJetBackground_bound n ha H
  refine ⟨C, hC, fun g D x hjets hell => ?_⟩
  rw [← differenceEnergyJetBackground_spatialJet D x]
  apply hbound
  · have hH := (norm_nonneg (iteratedFDeriv ℝ 0 g.euclideanCoefficients x)).trans
      (hjets 0 (by omega))
    apply (pi_norm_le_iff_of_nonneg hH).mpr
    intro j
    exact hjets j (by omega)
  · exact hell

end PoincareMT.M34
