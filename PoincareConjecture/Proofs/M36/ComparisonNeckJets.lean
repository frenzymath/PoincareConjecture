import PoincareConjecture.Proofs.M36.CenteredNeckMetric
import PoincareConjecture.Proofs.M36.AdaptedPolar
import PoincareConjecture.Proofs.M36.RadialWeights
import PoincareConjecture.Proofs.M36.ComparisonCoordinateJets
import PoincareConjecture.Proofs.M36.ComparisonPullback
import PoincareConjecture.Proofs.M36.CylinderAllOrderBounds
import PoincareConjecture.Proofs.M36.SurgeryTransitionMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture.M36

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

noncomputable def comparisonCylinderMap (g₀ : StandardInitialMetric)
    (x : StandardCapSpace) : RoundCylinderSpace :=
  ((adaptedInverseCoordinates g₀ x).1, standardSurgeryHeight g₀ x)

noncomputable def comparisonNeckLift (g₀ : StandardInitialMetric)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) : StandardCapSpace → M :=
  N.coordinate_map ∘ comparisonCylinderMap g₀

theorem comparisonCylinderMap_contMDiffAt (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    ContMDiffAt (𝓡 3) IC ∞ (comparisonCylinderMap g₀) x := by
  have hA := (adaptedInverseCoordinates_contMDiffOn g₀ x (by simpa using hx)).contMDiffAt
    (isOpen_compl_singleton.mem_nhds (by simpa using hx))
  exact hA.fst.prodMk (standardSurgeryHeight_contDiffAt g₀ hx).contMDiffAt

theorem comparison_chart_source_nhds (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) {x : StandardCapSpace} (hx : x ≠ 0)
    (hchart : (adaptedInverseCoordinates g₀ x).1 ∈ (chartAt E₂ theta).source) :
    ∀ᶠ p in nhds x, (adaptedInverseCoordinates g₀ p).1 ∈ (chartAt E₂ theta).source := by
  have hA := (adaptedInverseCoordinates_contMDiffOn g₀ x (by simpa using hx)).contMDiffAt
    (isOpen_compl_singleton.mem_nhds (by simpa using hx))
  exact hA.fst.continuousAt.preimage_mem_nhds ((chartAt E₂ theta).open_source.mem_nhds hchart)

theorem comparisonCenteredCoordinates_height (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) (s : ℝ) (p : StandardCapSpace) :
    cylinderHeightCovector (comparisonCenteredCoordinates g₀ theta s p) + s =
      standardSurgeryHeight g₀ p := by
  change (cylinderEuclideanEquiv (cylinderEuclideanEquiv.symm
    ((chartAt E₂ theta) (adaptedInverseCoordinates g₀ p).1,
      standardSurgeryHeight g₀ p - s))).2 + s = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact sub_add_cancel _ _

theorem centeredCylinderLift_comparisonCoordinates (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) (s : ℝ) {p : StandardCapSpace}
    (hchart : (adaptedInverseCoordinates g₀ p).1 ∈ (chartAt E₂ theta).source) :
    centeredCylinderLift theta s (comparisonCenteredCoordinates g₀ theta s p) =
      comparisonCylinderMap g₀ p := by
  apply Prod.ext
  · change (chartAt E₂ theta).symm ((cylinderEuclideanEquiv (cylinderEuclideanEquiv.symm
      ((chartAt E₂ theta) (adaptedInverseCoordinates g₀ p).1,
        standardSurgeryHeight g₀ p - s))).1) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact (chartAt E₂ theta).left_inv hchart
  · exact comparisonCenteredCoordinates_height g₀ theta s p

theorem adaptedClippedCollapse_comparisonCylinderMap (g₀ : StandardInitialMetric)
    {x : StandardCapSpace} (hx : x ≠ 0) :
    adaptedClippedCollapse g₀ (surgeryCapRadius g₀) (comparisonCylinderMap g₀ x) = x := by
  have hr : 0 < radialArclength g₀ ‖x‖ := radialArclength_pos g₀ (norm_pos_iff.mpr hx)
  have hs : (comparisonCylinderMap g₀ x).2 < surgeryCapRadius g₀ := by
    change g₀.cylindrical_end.radius + 4 - radialArclength g₀ ‖x‖ <
      g₀.cylindrical_end.radius + 4
    linarith
  rw [adaptedClippedCollapse_of_lt g₀ _ _ hs]
  have hh : surgeryCapRadius g₀ - standardSurgeryHeight g₀ x =
      (adaptedInverseCoordinates g₀ x).2 := by
    dsimp [surgeryCapRadius, standardSurgeryHeight, adaptedInverseCoordinates]
    ring
  change adaptedPolarPoint g₀ ((adaptedInverseCoordinates g₀ x).1,
    surgeryCapRadius g₀ - standardSurgeryHeight g₀ x) = x
  rw [hh]
  exact adaptedPolarPoint_inverse g₀ x hx

noncomputable def comparisonCenteredStandardLift (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) (s : ℝ) : E₃ → StandardCapSpace :=
  adaptedClippedCollapse g₀ (surgeryCapRadius g₀) ∘ centeredCylinderLift theta s

theorem comparisonCenteredStandardLift_contMDiffAt (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃}
    (hp : cylinderHeightCovector p + s < 2) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (comparisonCenteredStandardLift g₀ theta s) p := by
  have htip : (centeredCylinderLift theta s p).2 < surgeryCapRadius g₀ := by
    change cylinderHeightCovector p + s < g₀.cylindrical_end.radius + 4
    linarith [g₀.cylindrical_end.radius_pos]
  exact ((adaptedClippedCollapse_contMDiffOn g₀ _ _ htip).contMDiffAt
    ((isOpen_lt continuous_snd continuous_const).mem_nhds htip)).comp p
      (centeredCylinderLift_contMDiff theta s p)

theorem comparisonCenteredStandardLift_pullback (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) (s : ℝ) {p : E₃}
    (hp : cylinderHeightCovector p + s < 2) :
    g₀.metric.pullbackCoefficients (comparisonCenteredStandardLift g₀ theta s) p =
      cylinderModelField p := by
  let A := centeredCylinderLift theta s
  have htip : (A p).2 < surgeryCapRadius g₀ := by
    change cylinderHeightCovector p + s < g₀.cylindrical_end.radius + 4
    linarith [g₀.cylindrical_end.radius_pos]
  have hclip := ((adaptedClippedCollapse_contMDiffOn g₀ _ (A p) htip).contMDiffAt
    ((isOpen_lt continuous_snd continuous_const).mem_nhds htip)).mdifferentiableAt (by simp)
  have hA := (centeredCylinderLift_contMDiff theta s p).mdifferentiableAt (by simp)
  have hd := mfderiv_comp p hclip hA
  apply euclideanThree_bilinear_ext
  intro i j
  change g₀.metric.inner (adaptedClippedCollapse g₀ (surgeryCapRadius g₀) (A p))
    (mfderiv (𝓡 3) (𝓡 3) (adaptedClippedCollapse g₀ (surgeryCapRadius g₀) ∘ A) p
      (EuclideanSpace.basisFun (Fin 3) ℝ i))
    (mfderiv (𝓡 3) (𝓡 3) (adaptedClippedCollapse g₀ (surgeryCapRadius g₀) ∘ A) p
      (EuclideanSpace.basisFun (Fin 3) ℝ j)) = _
  rw [hd]
  change g₀.metric.inner (adaptedClippedCollapse g₀ (surgeryCapRadius g₀) (A p))
    (mfderiv IC (𝓡 3) (adaptedClippedCollapse g₀ (surgeryCapRadius g₀)) (A p)
      (mfderiv (𝓡 3) IC A p (EuclideanSpace.basisFun (Fin 3) ℝ i)))
    (mfderiv IC (𝓡 3) (adaptedClippedCollapse g₀ (surgeryCapRadius g₀)) (A p)
      (mfderiv (𝓡 3) IC A p (EuclideanSpace.basisFun (Fin 3) ℝ j))) = _
  rw [adaptedClippedCollapse_bilinear_transition g₀ (A p) hp]
  exact centeredCylinderLift_basis_gram theta s p i j

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem comparisonNeckLift_contMDiffAt (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) {x : StandardCapSpace} (hx : x ≠ 0)
    (hheight : standardSurgeryHeight g₀ x ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (comparisonNeckLift g₀ N) x :=
  (neck_coordinate_contMDiffAt N (z := comparisonCylinderMap g₀ x)
    ⟨Set.mem_univ _, hheight⟩).comp x (comparisonCylinderMap_contMDiffAt g₀ hx)

theorem comparisonNeckError_contDiffAt (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) {x : StandardCapSpace} (hx : x ≠ 0)
    (hheight : standardSurgeryHeight g₀ x ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContDiffAt ℝ ∞ (fun p => (normalizedNeckMetric N).pullbackCoefficients
      (comparisonNeckLift g₀ N) p - g₀.metric.euclideanCoefficients p) x :=
  ((normalizedNeckMetric N).contDiffAt_pullbackCoefficients
    (comparisonNeckLift_contMDiffAt g₀ N hx hheight)).sub
      (g₀.metric.contDiffAt_euclideanCoefficients x)

theorem pullbackCoefficients_congr_germ (g : RiemannianMetric 3 M)
    {f k : E₃ → M} {x : E₃} (heq : f =ᶠ[nhds x] k) :
    g.pullbackCoefficients f x = g.pullbackCoefficients k x := by
  have hd := heq.mfderiv_eq (I := 𝓡 3) (I' := 𝓡 3)
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  change g.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
    (mfderiv (𝓡 3) (𝓡 3) f x w) = _
  rw [heq.self_of_nhds, hd]
  rfl

theorem comparisonNeckLift_pullbackCentered (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) (theta : UnitTwoSphere) (s : ℝ)
    {x : StandardCapSpace} (hx : x ≠ 0)
    (hchart : (adaptedInverseCoordinates g₀ x).1 ∈ (chartAt E₂ theta).source)
    (hheight : standardSurgeryHeight g₀ x ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    (normalizedNeckMetric N).pullbackCoefficients (comparisonNeckLift g₀ N) x =
      (centeredCylinderMetric (fun z v w => normalizedNeckForm N z v w) theta s
        (comparisonCenteredCoordinates g₀ theta s x)).bilinearComp
          (fderiv ℝ (comparisonCenteredCoordinates g₀ theta s) x)
          (fderiv ℝ (comparisonCenteredCoordinates g₀ theta s) x) := by
  let Phi := comparisonCenteredCoordinates g₀ theta s
  have hPhi := comparisonCenteredCoordinates_contDiffAt_of_mem g₀ theta s hx hchart
  have hmem : Phi x ∈ centeredNeckDomain N s := by
    change cylinderHeightCovector (Phi x) + s ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
    rw [comparisonCenteredCoordinates_height]
    exact hheight
  have heq : centeredNeckLift N theta s ∘ Phi =ᶠ[nhds x] comparisonNeckLift g₀ N := by
    filter_upwards [comparison_chart_source_nhds g₀ theta hx hchart] with p hp
    change N.coordinate_map (centeredCylinderLift theta s (Phi p)) =
      N.coordinate_map (comparisonCylinderMap g₀ p)
    rw [centeredCylinderLift_comparisonCoordinates g₀ theta s hp]
  rw [← pullbackCoefficients_congr_germ (normalizedNeckMetric N) heq,
    pullbackCoefficients_comp _ (centeredNeckLift_contMDiffAt N theta s hmem) hPhi,
    normalizedNeckMetric_pullbackCoefficients N theta s hmem]

theorem comparisonStandard_pullbackCentered (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) (s : ℝ) {x : StandardCapSpace} (hx : x ≠ 0)
    (hchart : (adaptedInverseCoordinates g₀ x).1 ∈ (chartAt E₂ theta).source)
    (hheight : standardSurgeryHeight g₀ x < 2) :
    g₀.metric.euclideanCoefficients x =
      (cylinderModelField (comparisonCenteredCoordinates g₀ theta s x)).bilinearComp
        (fderiv ℝ (comparisonCenteredCoordinates g₀ theta s) x)
        (fderiv ℝ (comparisonCenteredCoordinates g₀ theta s) x) := by
  let Phi := comparisonCenteredCoordinates g₀ theta s
  have hPhi := comparisonCenteredCoordinates_contDiffAt_of_mem g₀ theta s hx hchart
  have hh : cylinderHeightCovector (Phi x) + s < 2 := by
    rw [comparisonCenteredCoordinates_height]
    exact hheight
  have heq : comparisonCenteredStandardLift g₀ theta s ∘ Phi =ᶠ[nhds x] id := by
    filter_upwards [comparison_chart_source_nhds g₀ theta hx hchart,
      isOpen_compl_singleton.mem_nhds (by simpa using hx : x ∈ ({0}ᶜ : Set E₃))] with p hp hp0
    change adaptedClippedCollapse g₀ (surgeryCapRadius g₀)
      (centeredCylinderLift theta s (Phi p)) = p
    rw [centeredCylinderLift_comparisonCoordinates g₀ theta s hp]
    exact adaptedClippedCollapse_comparisonCylinderMap g₀ (by simpa using hp0)
  have hid : g₀.metric.pullbackCoefficients id x = g₀.metric.euclideanCoefficients x := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    change g₀.metric.inner x (mfderiv (𝓡 3) (𝓡 3) id x v)
      (mfderiv (𝓡 3) (𝓡 3) id x w) = _
    rw [mfderiv_id]
    rfl
  rw [← hid, ← pullbackCoefficients_congr_germ g₀.metric heq,
    pullbackCoefficients_comp _ (comparisonCenteredStandardLift_contMDiffAt g₀ theta s hh) hPhi,
    comparisonCenteredStandardLift_pullback g₀ theta s hh]

theorem comparisonNeckError_centered_germ (g₀ : StandardInitialMetric)
    (N : EpsilonNeck g) {x : StandardCapSpace} (hx : x ≠ 0)
    (hheight : standardSurgeryHeight g₀ x ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hx₂ : standardSurgeryHeight g₀ x < 2) :
    (fun p => (normalizedNeckMetric N).pullbackCoefficients (comparisonNeckLift g₀ N) p -
      g₀.metric.euclideanCoefficients p) =ᶠ[nhds x]
      fun p => (centeredCylinderError (fun z v w => normalizedNeckForm N z v w)
        (adaptedInverseCoordinates g₀ x).1 (standardSurgeryHeight g₀ x)
        (comparisonCenteredCoordinates g₀ (adaptedInverseCoordinates g₀ x).1
          (standardSurgeryHeight g₀ x) p)).bilinearComp
            (fderiv ℝ (comparisonCenteredCoordinates g₀ (adaptedInverseCoordinates g₀ x).1
              (standardSurgeryHeight g₀ x)) p)
            (fderiv ℝ (comparisonCenteredCoordinates g₀ (adaptedInverseCoordinates g₀ x).1
              (standardSurgeryHeight g₀ x)) p) := by
  let theta := (adaptedInverseCoordinates g₀ x).1
  let s := standardSurgeryHeight g₀ x
  have hnonzero : ∀ᶠ p in nhds x, p ≠ (0 : StandardCapSpace) :=
    isOpen_compl_singleton.mem_nhds hx
  have hneck : ∀ᶠ p in nhds x,
      standardSurgeryHeight g₀ p ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (standardSurgeryHeight_continuous g₀).continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds hheight)
  have htwo : ∀ᶠ p in nhds x, standardSurgeryHeight g₀ p < 2 :=
    (isOpen_lt (standardSurgeryHeight_continuous g₀) continuous_const).mem_nhds hx₂
  filter_upwards [hnonzero, hneck, htwo,
    comparison_chart_source_nhds g₀ theta hx (mem_chart_source E₂ _)] with p hp hpneck hp₂ hpchart
  rw [comparisonNeckLift_pullbackCentered g₀ N theta s hp hpchart hpneck,
    comparisonStandard_pullbackCentered g₀ theta s hp hpchart hp₂]
  have herr := congrFun (centeredCylinderMetric_sub_model
    (fun z v w => normalizedNeckForm N z v w) theta s)
      (comparisonCenteredCoordinates g₀ theta s p)
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  simp only [sub_apply, ContinuousLinearMap.bilinearComp_apply]
  rw [← herr]
  rfl

theorem exists_comparisonNeckMetric_jet_bound (g₀ : StandardInitialMetric)
    {K : Set StandardCapSpace} (hK : IsCompact K) (hK0 : ∀ x ∈ K, x ≠ 0)
    (hKheight : ∀ x ∈ K, standardSurgeryHeight g₀ x < 2) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {M' : Type u} [TopologicalSpace M'] [ChartedSpace E₃ M'] [IsManifold (𝓡 3) ∞ M']
        {g' : RiemannianMetric 3 M'} (N : EpsilonNeck g'),
        m ≤ ⌊N.epsilon⁻¹⌋₊ →
        (∀ x ∈ K, standardSurgeryHeight g₀ x ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) →
        ∀ x ∈ K, ∀ j : ℕ, j ≤ m →
          ‖iteratedFDeriv ℝ j (fun p =>
            (normalizedNeckMetric N).pullbackCoefficients (comparisonNeckLift g₀ N) p -
              g₀.metric.euclideanCoefficients p) x‖ ≤ C * N.epsilon := by
  classical
  choose D hD hDbound using fun j : Fin (m + 1) => exists_centeredCylinderError_jet_bound j
  let D0 : ℝ := 1 + ∑ j : Fin (m + 1), D j
  have hD0 : 0 < D0 := by
    have hsum : 0 ≤ ∑ j : Fin (m + 1), D j :=
      Finset.sum_nonneg (fun j _ => (hD j).le)
    dsimp [D0]
    linarith
  have hDle (j : Fin (m + 1)) : D j ≤ D0 := by
    have h := Finset.single_le_sum (f := D) (fun j _ => (hD j).le) (Finset.mem_univ j)
    dsimp [D0]
    linarith
  obtain ⟨Q, hQ, hQbound⟩ := exists_comparisonCenteredCoordinates_jet_bound g₀ hK hK0 (m + 1)
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  let L : ℝ := 2 ^ m * 2 ^ m * m.factorial * Q ^ m * Q * Q
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨1 + L * D0, le_add_of_nonneg_right (mul_nonneg hL hD0.le), ?_⟩
  intro M' _ _ _ g' N horder hheight x hx j hj
  let B : RoundCylinderTwoTensor := fun z v w => normalizedNeckForm N z v w
  let z : RoundCylinderSpace := comparisonCylinderMap g₀ x
  let Phi := comparisonCenteredCoordinates g₀ z.1 z.2
  have hB : RoundCylinderClose N.epsilon 0 B := N.metric_comparison.close
  have hz : z.2 ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := hheight x hx
  have hPhi0 : Phi x = 0 := comparisonCenteredCoordinates_self g₀ x
  have hPhi : ContDiffAt ℝ ∞ Phi x := comparisonCenteredCoordinates_contDiffAt g₀ (hK0 x hx)
  have hBs : ContDiffAt ℝ ∞ (centeredCylinderError B z.1 z.2) (Phi x) := by
    rw [hPhi0]
    exact centeredCylinderError_contDiffAt hB z hz
  have hBj (l : ℕ) (hl : l ≤ j) :
      ‖iteratedFDeriv ℝ l (centeredCylinderError B z.1 z.2) (Phi x)‖ ≤ D0 * N.epsilon := by
    rw [hPhi0]
    let l' : Fin (m + 1) := ⟨l, Nat.lt_succ_of_le (hl.trans hj)⟩
    exact (hDbound l' N.epsilon_pos hB ((hl.trans hj).trans horder) z hz).trans
      (mul_le_mul_of_nonneg_right (hDle l') N.epsilon_pos.le)
  have hjet := norm_iteratedFDeriv_bilinearPullback_at hPhi hBs j
    (mul_nonneg hD0.le N.epsilon_pos.le) hQ hBj
    (fun l _ hl => hQbound x hx l (by omega))
  have hconstant : (2 : ℝ) ^ j * 2 ^ j * j.factorial * Q ^ j * Q * Q ≤ L := by
    dsimp [L]
    gcongr <;> norm_num
  have heq := comparisonNeckError_centered_germ g₀ N (hK0 x hx) hz (hKheight x hx)
  rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
  exact hjet.trans ((mul_le_mul_of_nonneg_right hconstant
    (mul_nonneg hD0.le N.epsilon_pos.le)).trans (by nlinarith [N.epsilon_pos]))

end PoincareConjecture.M36
