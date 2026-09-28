import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.Scaled
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Field
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.TraceIntegral








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral BigOperators

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum.Variation ReducedLengthMinimum.Variation.Geometry
open ReducedLengthMinimum.Variation.Frame

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem curvature_add_minimum_le_two_of_adapted_frame (K : AncientKappaSolution 2 M)
    {τ m : ℝ} (hτ : 0 < τ) (q : BackwardTimePath K.flow 0 0 τ)
    (S : SqrtRegularPath q)
    (E : ParametricAlongCurveExtensionOn (Icc 0 (Real.sqrt τ)) S.curve
      (curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ))))
    (hmin : ∀ r : BackwardTimePath K.flow 0 0 τ, r.curve 0 = q.curve 0 →
      backwardLLength K.flow 0 0 τ q.curve ≤ backwardLLength K.flow 0 0 τ r.curve)
    (heuler : ∀ s ∈ Ioo 0 (Real.sqrt τ),
      regularizedLGeodesicEquation K.flow 0 S.curve (Icc 0 (Real.sqrt τ)) E s)
    (hterminal : curveVelocityWithin (n := 2) S.curve (Icc 0 (Real.sqrt τ)) (Real.sqrt τ) = 0)
    (haction : backwardLLength K.flow 0 0 τ q.curve = 2 * Real.sqrt τ * m)
    (U : Set ℝ) (hU : IsOpen U) (hCU : Icc 0 (Real.sqrt τ) ⊆ U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) ∞ S.curve U)
    (P : Fin 2 → ∀ s, TangentSpace (𝓡 2) (S.curve s))
    (hP : ∀ i, IsAdaptedFieldOn K.flow 0 S.curve (P i) U)
    (horth : ∀ s ∈ Icc 0 (Real.sqrt τ), ∀ i j,
      (K.flow.metric (0 - s ^ 2)).inner (S.curve s) (P i s) (P j s) =
        if i = j then 1 else 0) :
    τ * (K.flow.connection (-τ)).scalarCurvature (S.curve (Real.sqrt τ)) + m ≤ 2 := by
  classical
  let c := Real.sqrt τ
  let C := Icc (0 : ℝ) c
  have hc : 0 < c := Real.sqrt_pos.mpr hτ
  let EP (i : Fin 2) : ParametricAlongCurveExtensionOn U S.curve (P i) :=
    Classical.choice (exists_parametricSectionExtension hU S.curve hα (P i) (hP i).smooth)
  let Y (i : Fin 2) : ∀ s, TangentSpace (𝓡 2) (S.curve s) := fun s ↦ (s / c) • P i s
  let HY (i : Fin 2) : ParametricAlongCurveExtensionOn U S.curve (Y i) :=
    smulParametricExtension (EP i) (fun s ↦ s / c) (contDiff_id.div_const c)
  let H (i : Fin 2) : ParametricAlongCurveExtensionOn C S.curve (Y i) :=
    restrictParametricSectionExtension hCU (HY i)
  let d (i : Fin 2) := fieldIndexDensity K.flow 0 S.curve C (Y i) (H i)
  let D := fun s ↦ ∑ i : Fin 2, d i s
  have hindex (i : Fin 2) : IntervalIntegrable (d i) volume 0 c ∧
      0 ≤ ∫ s in (0 : ℝ)..c, d i s := by
    exact K.fieldIndexDensity_integrable_and_integral_nonneg S E hmin heuler hterminal
      (Y i) U hU hCU (parametricExtension_field_contMDiffOn (HY i) hα)
      (by simp only [Y, zero_div, zero_smul]) (H i)
  have hD : IntervalIntegrable D volume 0 c :=
    IntervalIntegrable.sum Finset.univ (fun i _ ↦ (hindex i).1)
  have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..c, D s := by
    rw [show D = fun s ↦ ∑ i : Fin 2, d i s from rfl,
      intervalIntegral.integral_finsetSum (fun i _ ↦ (hindex i).1)]
    exact Finset.sum_nonneg (fun i _ ↦ (hindex i).2)
  apply K.curvature_add_minimum_le_two_of_index_trace hτ q S E heuler hterminal
    haction D hD ?_ hnonneg
  intro s hs
  have hsC : s ∈ C := Ioo_subset_Icc_self hs
  have hCs : UniqueDiffWithinAt ℝ C s := uniqueDiffOn_Icc hc s hsC
  let A := curveVelocityWithin (n := 2) S.curve C s
  let L := K.flow.connection (0 - s ^ 2)
  have hDY (i : Fin 2) :
      pullbackCovariantDerivative K.flow (fun r ↦ 0 - r ^ 2) S.curve (Y i) C (H i) s =
        (1 / c - s * (s / c) * L.scalarCurvature (S.curve s)) • P i s := by
    exact pullback_scaled_adapted_surface K.flow 0 S.curve (P i)
      (restrictParametricSectionExtension hCU (EP i)) c (H i) hU hα (hP i)
      hsC (hCU hsC) hCs (ancient_squareTime_mem_interior s)
  obtain ⟨e, he⟩ := exists_orthonormalBasis_eq (K.flow.metric (0 - s ^ 2))
    (S.curve s) (fun i ↦ P i s) (horth s hsC)
  have htrace := surface_scaled_index_trace L (S.curve s) A s (ne_of_gt hc) e
  simp only [he] at htrace
  have hsum : c ^ 2 * D s =
      2 - 4 * s ^ 2 * L.scalarCurvature (S.curve s) +
        2 * s ^ 4 * (L.laplacian L.scalarCurvature (S.curve s) +
          L.scalarCurvature (S.curve s) ^ 2) - s ^ 2 * L.ricci (S.curve s) A A := by
    convert htrace using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [d, fieldIndexDensity]
    rw [hDY i]
  exact hsum.trans (congrArg (fun t : ℝ ↦
    2 - 4 * s ^ 2 * (K.flow.connection t).scalarCurvature (S.curve s) +
      2 * s ^ 4 * ((K.flow.connection t).laplacian
        (K.flow.connection t).scalarCurvature (S.curve s) +
        (K.flow.connection t).scalarCurvature (S.curve s) ^ 2) -
      s ^ 2 * (K.flow.connection t).ricci (S.curve s) A A) (zero_sub (s ^ 2)))

end PoincareConjecture.AncientKappaSolution
