import PoincareConjecture.Proofs.M34.Standard.CurvatureJetRealization
import PoincareConjecture.Proofs.M03.ConnectionNativeTime













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap



noncomputable def raisedCurvatureTwoJet {n : ℕ} (J : MetricTwoJet n)
    (u v w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  J.1.inverse (∑ i : Fin n,
    (jetCurvature J u v (EuclideanSpace.single i 1) w) • EuclideanSpace.proj i)



theorem contDiffAt_raisedCurvatureTwoJet {n : ℕ} {J : MetricTwoJet n}
    (hJ : J.1.IsInvertible) (u v w : EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ ∞ (fun K => raisedCurvatureTwoJet K u v w) J := by
  have hI : ContDiffAt ℝ ∞ (fun K : MetricTwoJet n => K.1.inverse) J :=
    hJ.contDiffAt_map_inverse.comp J contDiffAt_fst
  apply hI.clm_apply
  apply ContDiffAt.sum
  intro i _
  exact (contDiffAt_jetCurvature hJ _ _ _ _).smul contDiffAt_const



noncomputable def inverseMetricJetArray (n : ℕ)
    (J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 2)
    (i j : Fin n) : ℝ :=
  EuclideanSpace.proj i ((twoJetProjection n J).1.inverse (EuclideanSpace.proj j))



noncomputable def connectionJetArray (n : ℕ)
    (J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 2)
    (i j l : Fin n) : ℝ :=
  EuclideanSpace.proj l (jetChristoffel (twoJetProjection n J)
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))




noncomputable def raisedCurvatureJetArray (n : ℕ)
    (J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 2)
    (l j k m : Fin n) : ℝ :=
  EuclideanSpace.proj l (raisedCurvatureTwoJet (twoJetProjection n J)
    (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) (EuclideanSpace.single m 1))



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




noncomputable def differenceEnergyJetBackground (n : ℕ)
    (J : Jet (EuclideanSpace ℝ (Fin n)) (MetricCoefficient n) 3) :=
  ((inverseMetricJetArray n (truncate 2 J), connectionJetArray n (truncate 2 J)),
    (raisedCurvatureJetArray n (truncate 2 J), prolong 2 (raisedCurvatureJetArray n) J))




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




theorem raisedCurvatureTwoJet_metricTwoJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x u v w : EuclideanSpace ℝ (Fin n)) :
    raisedCurvatureTwoJet (metricTwoJet g.euclideanCoefficients x) u v w =
      D.curvature x u v w := by
  unfold raisedCurvatureTwoJet
  simp_rw [jetCurvature_metricTwoJet D]
  exact Proofs.M03.inverse_bilinear_reconstruct (g.inner_isInvertible x) _



theorem connectionJetArray_spatialJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) (i j l : Fin n) :
    connectionJetArray n (spatialJet 2
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients p.2) (0, x)) i j l =
      EuclideanSpace.proj l
        (D.euclideanConnection (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) x) := by
  simp only [connectionJetArray, twoJetProjection_spatialJet, jetChristoffel_metricTwoJet D]



theorem raisedCurvatureJetArray_spatialJet {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) (l j k m : Fin n) :
    raisedCurvatureJetArray n (spatialJet 2
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => g.euclideanCoefficients p.2) (0, x)) l j k m =
      EuclideanSpace.proj l (D.curvature x (EuclideanSpace.single j 1)
        (EuclideanSpace.single k 1) (EuclideanSpace.single m 1)) := by
  simp only [raisedCurvatureJetArray, twoJetProjection_spatialJet,
    raisedCurvatureTwoJet_metricTwoJet D]




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

end PoincareConjecture.M34
