import PoincareConjecture.Proofs.M32.Claim11_35.Evolving.CovariantJets
import PoincareConjecture.Proofs.M32.Neck.Spatial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.Realization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M32

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates

private noncomputable instance evolvingLinearNormedGroup :
    NormedAddCommGroup (E3 →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

private noncomputable instance evolvingLinearNormedSpace :
    NormedSpace ℝ (E3 →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

private noncomputable instance evolvingCoefficientNormedGroup :
    NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

private noncomputable instance evolvingCoefficientNormedSpace :
    NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}

private noncomputable def evolvingSpatialCoordinate
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0) :
    RoundCylinderSpace → (F.slice (t + tau / (N.scale⁻¹ ^ 2))).carrier :=
  fun z => N.time_cylinder.forward tau htau (N.coordinate_map z)

private noncomputable def evolvingEuclideanRechart
    {tau : ℝ} (htau : tau ∈ Ioc (-1) 0) : E3 ≃L[ℝ] V :=
  (RiemannianMetric.lineModelEquiv 2).symm.trans
    (evolvingCylinderAxialEquiv tau (lt_of_le_of_lt htau.2 zero_lt_one))

private theorem evolving_coordinate_map_mem (N : GeneralizedStrongNeck F t epsilon)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    N.coordinate_map z ∈ N.carrier := by
  let w : NeckDomain epsilon := (z.1, ⟨z.2, hz⟩)
  have h := (N.coordinate w).property
  simpa only [N.coordinate_map_eq w, w] using h

private theorem evolvingSpatialCoordinate_contMDiffAt
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0)
    {z : RoundCylinderSpace} (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (evolvingSpatialCoordinate N htau) z := by
  have hcoord := N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)
  have hforward := (N.time_cylinder.forward_smooth tau htau).contMDiffAt
    (N.carrier_open.mem_nhds (evolving_coordinate_map_mem N hz))
  exact hforward.comp z hcoord

private theorem evolvingChartCoordinate_contMDiffAt
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0)
    (q : UnitTwoSphere) {p : V} (hp : p.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ContMDiffAt 𝓘(ℝ, V) (𝓡 3) ∞
      (fun y => evolvingSpatialCoordinate N htau ((chartAt E2 q).symm y.1, y.2)) p :=
  (evolvingSpatialCoordinate_contMDiffAt N htau hp).comp p (cylinderChart_symm_smooth q p)

private theorem evolvingSpatialCoordinate_pullback_close
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0) :
    RoundCylinderClose epsilon tau (fun z v w => N.scale⁻¹ ^ 2 *
      roundCylinderPullback (F.metric (t + tau / (N.scale⁻¹ ^ 2)))
        (evolvingSpatialCoordinate N htau) z v w) := by
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := N.metric_comparison
  have hclose : RoundCylinderClose epsilon tau
      (generalizedCylinderPullback N.time_cylinder N.coordinate_map tau) :=
    ⟨hsmooth tau htau, bound, hbound, hjet tau htau⟩
  apply roundCylinderClose_congr_axial (hclose := hclose)
  intro z hz v w
  have hcoord := (N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
  have hforward := ((N.time_cylinder.forward_smooth tau htau).contMDiffAt
    (N.carrier_open.mem_nhds (evolving_coordinate_map_mem N hz))).mdifferentiableAt (by simp)
  simp only [generalizedCylinderPullback, dif_pos htau, GeneralizedFlowCylinder.pullbackInner,
    roundCylinderPullback, evolvingSpatialCoordinate]
  erw [mfderiv_comp_apply z hforward hcoord v, mfderiv_comp_apply z hforward hcoord w]

private theorem parametrizedCoefficients_affine
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (f : V → M) (L : E3 →L[ℝ] V) (p : V) (x : E3)
    (hf : MDifferentiableAt 𝓘(ℝ, V) (𝓡 3) f (p + L x)) :
    g.parametrizedCoefficients (fun y => f (p + L y)) x =
      (g.parametrizedCoefficients f (p + L x)).bilinearComp L L := by
  have ha : HasFDerivAt (fun y : E3 => p + L y) L x := L.hasFDerivAt.const_add p
  have hd := mfderiv_comp x hf ha.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv, ha.fderiv] at hd
  ext v w
  simp only [RiemannianMetric.parametrizedCoefficients_apply,
    ContinuousLinearMap.bilinearComp_apply]
  erw [hd]
  rfl

noncomputable def strongNeckEvolvingCoefficients
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0)
    (q : UnitTwoSphere) (z : ℝ) (x : E3) : E3 →L[ℝ] E3 →L[ℝ] ℝ :=
  let Q := N.scale⁻¹ ^ 2
  let L := evolvingEuclideanRechart htau
  let f : E3 → (F.slice (t + tau / Q)).carrier := fun y =>
    evolvingSpatialCoordinate N htau
      ((chartAt E2 q).symm ((0, z) + L y).1, ((0, z) + L y).2)
  (Q / (1 - tau)) • (F.metric (t + tau / Q)).parametrizedCoefficients f x

set_option maxHeartbeats 800000 in

private theorem strongNeckEvolvingCoefficients_contDiffAt
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0)
    (q : UnitTwoSphere) (z : ℝ) {x : E3}
    (hx : ((0, z) + evolvingEuclideanRechart htau x).2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ContDiffAt ℝ ∞ (strongNeckEvolvingCoefficients N htau q z) x := by
  have ha : ContMDiffAt (𝓡 3) 𝓘(ℝ, V) ∞
      (fun y => (0, z) + evolvingEuclideanRechart htau y) x :=
    (contDiffAt_const.add (evolvingEuclideanRechart htau).contDiff.contDiffAt).contMDiffAt
  have hf := (evolvingChartCoordinate_contMDiffAt N htau q hx).comp x ha
  have hcoeff := (F.metric (t + tau / (N.scale⁻¹ ^ 2))).contDiffAt_parametrizedCoefficients hf
  unfold strongNeckEvolvingCoefficients
  exact hcoeff.const_smul (N.scale⁻¹ ^ 2 / (1 - tau))

private theorem evolvingEuclideanRechart_basis {tau : ℝ} (htau : tau ∈ Ioc (-1) 0)
    (i : Fin 3) :
    evolvingEuclideanRechart htau (roundCylinderEuclideanBasis i) =
      (if i = 2 then Real.sqrt (1 - tau) else 1) • roundCylinderCoordinateBasis i := by
  change evolvingCylinderAxialEquiv tau (lt_of_le_of_lt htau.2 zero_lt_one)
    ((RiemannianMetric.lineModelEquiv 2).symm (roundCylinderEuclideanBasis i)) = _
  rw [lineModelEquiv_symm_roundCylinderEuclideanBasis]
  exact (evolving_model_axialNormalization ⟨htau.1.le, htau.2⟩).2.1 i

private theorem strongNeckEvolvingCoefficients_basis
    (N : GeneralizedStrongNeck F t epsilon) {tau : ℝ} (htau : tau ∈ Ioc (-1) 0)
    (q : UnitTwoSphere) (z : ℝ) (x : E3)
    (hx : ((0, z) + evolvingEuclideanRechart htau x).2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (i j : Fin 3) :
    strongNeckEvolvingCoefficients N htau q z x
        (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) =
      ((1 - tau)⁻¹ * (if i = 2 then Real.sqrt (1 - tau) else 1) *
        (if j = 2 then Real.sqrt (1 - tau) else 1)) *
        roundCylinderTensorCoefficient
          (fun y v w => N.scale⁻¹ ^ 2 *
            roundCylinderPullback (F.metric (t + tau / (N.scale⁻¹ ^ 2)))
              (evolvingSpatialCoordinate N htau) y v w)
          (chartAt E2 q) ((0, z) + evolvingEuclideanRechart htau x) i j := by
  let g := F.metric (t + tau / (N.scale⁻¹ ^ 2))
  let f := fun p : V => evolvingSpatialCoordinate N htau ((chartAt E2 q).symm p.1, p.2)
  have hf := (evolvingChartCoordinate_contMDiffAt N htau q hx).mdifferentiableAt (by simp)
  have heq := parametrizedCoefficients_affine g f
    (evolvingEuclideanRechart htau).toContinuousLinearMap (0, z) x hf
  have hcoeff := roundCylinderTensorCoefficient_pullback_eq g q
    (evolvingSpatialCoordinate N htau) ((0, z) + evolvingEuclideanRechart htau x)
    ((evolvingSpatialCoordinate_contMDiffAt N htau hx).mdifferentiableAt (by simp)) i j
  change (N.scale⁻¹ ^ 2 / (1 - tau)) *
    g.parametrizedCoefficients (fun y => f ((0, z) + evolvingEuclideanRechart htau y)) x
      (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) = _
  erw [heq]
  simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe,
    evolvingEuclideanRechart_basis, map_smul, smul_apply, smul_eq_mul]
  change (N.scale⁻¹ ^ 2 / (1 - tau)) *
    ((if j = 2 then Real.sqrt (1 - tau) else 1) *
      ((if i = 2 then Real.sqrt (1 - tau) else 1) *
        g.parametrizedCoefficients f ((0, z) + evolvingEuclideanRechart htau x)
          (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j))) =
    _ * (N.scale⁻¹ ^ 2 * roundCylinderTensorCoefficient
      (roundCylinderPullback g (evolvingSpatialCoordinate N htau))
        (chartAt E2 q) ((0, z) + evolvingEuclideanRechart htau x) i j)
  rw [hcoeff]
  simp only [RiemannianMetric.parametrizedCoefficients_apply, f, div_eq_mul_inv]
  ring

private theorem exists_strongNeck_evolving_scalar_fourJet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ},
      ∀ N : GeneralizedStrongNeck F t epsilon, epsilon ≤ 1 / 4 →
        ∀ {tau : ℝ} (htau : tau ∈ Ioc (-1) 0) (q : UnitTwoSphere) {z : ℝ},
          z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ → ∀ r : ℕ, r ≤ 4 → ∀ i j : Fin 3,
            ‖iteratedFDeriv ℝ r (fun x =>
              strongNeckEvolvingCoefficients N htau q z x
                (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
              roundCylinderEuclideanCoefficients x
                (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) 0‖ ≤
                  C * epsilon := by
  obtain ⟨C, hC, hbound⟩ := exists_evolving_covariant_fourJet_bound
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  let A := max 1 ‖T.toContinuousLinearMap‖
  have hA : 1 ≤ A := le_max_left _ _
  refine ⟨64 * C * A ^ 4, by positivity, ?_⟩
  intro F t epsilon N hsmall tau htau q z hz r hr i j
  let L := evolvingEuclideanRechart htau
  let B : RoundCylinderTwoTensor := fun y v w => N.scale⁻¹ ^ 2 *
    roundCylinderPullback (F.metric (t + tau / (N.scale⁻¹ ^ 2)))
      (evolvingSpatialCoordinate N htau) y v w
  have hB : RoundCylinderClose epsilon tau B := evolvingSpatialCoordinate_pullback_close N htau
  let E : V → ℝ := fun p => roundCylinderTensorCoefficient B (chartAt E2 q) p i j -
    roundCylinderGram tau (chartAt E2 q) p i j
  let m : ℝ := (1 - tau)⁻¹ * (if i = 2 then Real.sqrt (1 - tau) else 1) *
    (if j = 2 then Real.sqrt (1 - tau) else 1)
  have ha : 1 ≤ 1 - tau := by linarith [htau.2]
  have hsqrt : Real.sqrt (1 - tau) ≤ 2 := by
    have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 - tau)
    have hn := Real.sqrt_nonneg (1 - tau)
    nlinarith [htau.1]
  have hlambda (a : Fin 3) : |(if a = 2 then Real.sqrt (1 - tau) else 1)| ≤ 2 := by
    split_ifs
    · simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using hsqrt
    · norm_num
  have hm : |m| ≤ 4 := by
    dsimp only [m]
    rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
    calc
      _ ≤ 1 * 2 * 2 := mul_le_mul
        (mul_le_mul (inv_le_one_of_one_le₀ ha) (hlambda i) (abs_nonneg _) zero_le_one)
        (hlambda j) (abs_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  have hL : ‖L.toContinuousLinearMap‖ ≤ 2 * A := by
    have hs := (evolving_model_axialNormalization ⟨htau.1.le, htau.2⟩).1
    change ‖(evolvingCylinderAxialEquiv tau (lt_of_le_of_lt htau.2 zero_lt_one) : V →L[ℝ] V).comp
      T.toContinuousLinearMap‖ ≤ 2 * A
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hs (le_max_right _ _) (norm_nonneg _) (by norm_num))
  have hpow : ‖L.toContinuousLinearMap‖ ^ r ≤ 16 * A ^ 4 := by
    calc
      _ ≤ (2 * A) ^ r := pow_le_pow_left₀ (norm_nonneg _) hL r
      _ ≤ (2 * A) ^ 4 := pow_le_pow_right₀ (by linarith) hr
      _ = _ := by ring
  have hnear : ∀ᶠ x : E3 in 𝓝 0,
      ((0, z) + L x).2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    have hc : ContinuousAt (fun x : E3 => ((0, z) + L x).2) 0 :=
      (continuous_snd.comp (continuous_const.add L.continuous)).continuousAt
    exact hc.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by simpa only [map_zero, add_zero] using hz))
  have heq : (fun x : E3 => m * E ((0, z) + L x)) =ᶠ[𝓝 0]
      (fun x => strongNeckEvolvingCoefficients N htau q z x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) -
        roundCylinderEuclideanCoefficients x
          (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j)) := by
    filter_upwards [hnear] with x hx
    rw [strongNeckEvolvingCoefficients_basis N htau q z x hx i j,
      roundCylinderEuclideanCoefficients_basis q 0 x i j]
    have hmodel := (evolving_model_axialNormalization ⟨htau.1.le, htau.2⟩).2.2
      q z (T x) i j
    change m * roundCylinderGram tau (chartAt E2 q) ((0, z) + L x) i j =
      roundCylinderGram 0 (chartAt E2 q) (T x) i j at hmodel
    simp only [Prod.mk_zero_zero, zero_add]
    dsimp only [E]
    rw [mul_sub, hmodel]
  have hE : ContDiffAt ℝ ∞ E (0, z) :=
    evolving_covariant_contDiffAt (lt_of_le_of_lt htau.2 zero_lt_one) hB q hz 0 ![i, j]
  have hEbound : ‖iteratedFDeriv ℝ r E (0, z)‖ ≤ C * epsilon :=
    hbound N.epsilon_pos hsmall ⟨htau.1.le, htau.2⟩ hB q hz r 0 (by omega) ![i, j]
  have hcomp := Poincare.Analysis.Calculus.norm_iteratedFDeriv_comp_continuousLinearEquiv_le
    L (fun p => E ((0, z) + p)) r 0
  simp only [map_zero, iteratedFDeriv_comp_add_left, add_zero] at hcomp
  have hnorm := hcomp.trans (mul_le_mul hEbound hpow (pow_nonneg (norm_nonneg _) _)
    (mul_nonneg hC.le N.epsilon_pos.le))
  have hsmooth : ContDiffAt ℝ ∞ (fun x : E3 => E ((0, z) + L x)) 0 := by
    have hE' : ContDiffAt ℝ ∞ E ((0, z) + L (0 : E3)) := by
      simpa only [map_zero, add_zero] using hE
    exact hE'.comp 0 (contDiffAt_const.add L.contDiff.contDiffAt)
  rw [← (heq.iteratedFDeriv ℝ r).self_of_nhds]
  change ‖iteratedFDeriv ℝ r (m • fun x : E3 => E ((0, z) + L x)) 0‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (hsmooth.of_le (by exact_mod_cast le_top)), norm_smul,
    Real.norm_eq_abs]
  exact (mul_le_mul hm hnorm (norm_nonneg _) (by norm_num)).trans_eq (by ring)

theorem exists_strongNeck_evolving_fourJet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ},
      ∀ N : GeneralizedStrongNeck F t epsilon, epsilon ≤ 1 / 4 →
        ∀ {tau : ℝ} (htau : tau ∈ Ioc (-1) 0) (q : UnitTwoSphere) {z : ℝ},
          z ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ → ∀ r : ℕ, r ≤ 4 →
            ‖iteratedFDeriv ℝ r (fun y => strongNeckEvolvingCoefficients N htau q z y -
              roundCylinderEuclideanCoefficients y) 0‖ ≤ C * epsilon := by
  obtain ⟨C, hC, hbound⟩ := exists_strongNeck_evolving_scalar_fourJet_bound.{u}
  refine ⟨9 * C, by positivity, ?_⟩
  intro F t epsilon N hsmall tau htau q z hz r hr
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).reindex ((finRotate 3).symm)
  have hb (i : Fin 3) : b i = roundCylinderEuclideanBasis i := by
    simp only [b, roundCylinderEuclideanBasis, OrthonormalBasis.reindex_apply,
      Module.Basis.reindex_apply, OrthonormalBasis.coe_toBasis]
  have hN : ContDiffAt ℝ ∞ (strongNeckEvolvingCoefficients N htau q z) 0 :=
    strongNeckEvolvingCoefficients_contDiffAt N htau q z
      (by simpa only [map_zero, add_zero] using hz)
  have h := SpacetimeBounds.norm_iteratedFDeriv_bilinear_le_of_components b
    (hN.sub contDiff_roundCylinderEuclideanCoefficients.contDiffAt) r
    (C := C * epsilon) (fun i j => ?_)
  · convert h using 1
    ring
  · simpa only [sub_apply, hb] using hbound N hsmall htau q hz r hr i j

end PoincareConjecture.M32
