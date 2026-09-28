import PoincareConjecture.Proofs.M08.VariationDerivativeData
import PoincareConjecture.Proofs.M08.VariationIntegral
import PoincareConjecture.Proofs.M08.VariationPaths
import PoincareConjecture.Proofs.M08.RegularizedAction
import PoincareConjecture.Statements.Ch04.CurvatureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u v

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance variationActionDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance variationActionDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance variationActionBilinGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance variationActionBilinSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 800000 in
theorem movingMetric_pair_contMDiffOn {X : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X] {S : Set X} {J : Set ℝ}
    (F : RicciFlow n M J) (time : X → ℝ) (α : X → M)
    (V W : ∀ z, TangentSpace (𝓡 n) (α z))
    (htime : ContMDiffOn (𝓘(ℝ, X)) (𝓘(ℝ, ℝ)) ∞ time S)
    (hα : ContMDiffOn (𝓘(ℝ, X)) (𝓡 n) ∞ α S)
    (hV : ContMDiffOn (𝓘(ℝ, X)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α z) (V z)) S)
    (hW : ContMDiffOn (𝓘(ℝ, X)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α z) (W z)) S)
    (hmem : MapsTo time S J) :
    ContMDiffOn (𝓘(ℝ, X)) (𝓘(ℝ, ℝ)) ∞
      (fun z ↦ (F.metric (time z)).inner (α z) (V z) (W z)) S := by
  have hmetric := F.smooth.comp (htime.prodMk hα) (fun z hz ↦ ⟨hmem hz, mem_univ _⟩)
  have hp := hmetric.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ) hV hW
  intro z hz
  simpa only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
    using (Bundle.contMDiffWithinAt_totalSpace.mp (hp z hz)).2

def variationSliceSqrtRegular {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) {u : ℝ} (hu : u ∈ V.parameterDomain) :
    SqrtRegularPath (variationPath V hu) where
  curve := fun s ↦ V.squareFamily s u
  domain := (fun s : ℝ ↦ (s, u)) ⁻¹' V.squareDomain
  open_domain := V.square_open.preimage (continuous_id.prodMk continuous_const)
  interval_subset := fun s hs ↦ V.square_contains ⟨hs, hu⟩
  smooth := V.square_smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
    (fun s hs ↦ hs)
  agrees := fun s hs ↦ V.square_agrees s hs u hu

def variationActionDensity {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (z : ℝ × ℝ) : ℝ :=
  regularizedLIntegrand F T (fun s ↦ V.squareFamily s z.2) z.1

theorem variationLLength_eq_squareAction {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) {u : ℝ} (hu : u ∈ V.parameterDomain) :
    variationLLength V u =
      ∫ s in Real.sqrt τ₁..Real.sqrt τ₂, variationActionDensity V (s, u) :=
  (regularizedLAction_eq_backwardLLength (variationSliceSqrtRegular V hu)).symm

set_option maxHeartbeats 1000000 in
theorem variationActionDensity_contDiffOn {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    {p : BackwardTimePath F T τ₁ τ₂} (V : LVariation F T τ₁ τ₂ p) :
    ContDiffOn ℝ ∞ (variationActionDensity V)
      (sqrtParameterInterval τ₁ τ₂ ×ˢ V.parameterDomain) := by
  let S := sqrtParameterInterval τ₁ τ₂ ×ˢ V.parameterDomain
  let H := fun z : ℝ × ℝ ↦ V.squareFamily z.1 z.2
  have hH : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓡 n) ∞ H S := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact V.square_smooth.mono V.square_contains
  have hA : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × ℝ ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (H z)
        (curveVelocity (n := n) (fun r ↦ H (r, z.2)) z.1)) S := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (contMDiffOn_curveVelocity_fst V.square_open H V.square_smooth).mono V.square_contains
  have ht : ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × ℝ ↦ T - z.1 ^ 2) S :=
    (contDiff_const.sub (contDiff_fst.pow 2)).contMDiff.contMDiffOn
  have hmem : MapsTo (fun z : ℝ × ℝ ↦ T - z.1 ^ 2) S J := by
    intro z hz
    apply p.time_mem
    have hz0 : 0 ≤ z.1 := (Real.sqrt_nonneg τ₁).trans hz.1.1
    constructor
    · nlinarith [Real.sq_sqrt p.nonnegative, Real.sqrt_nonneg τ₁, hz.1.1]
    · nlinarith [Real.sq_sqrt (p.nonnegative.trans p.ordered.le), Real.sqrt_nonneg τ₂, hz.1.2]
  have hg := (movingMetric_pair_contMDiffOn F (fun z : ℝ × ℝ ↦ T - z.1 ^ 2) H
    (fun z ↦ curveVelocity (n := n) (fun r ↦ H (r, z.2)) z.1)
    (fun z ↦ curveVelocity (n := n) (fun r ↦ H (r, z.2)) z.1) ht hH hA hA hmem).contDiffOn
  have hR := ((hM04.scalar_regular n M J F).comp (ht.prodMk hH)
    (fun z hz ↦ ⟨hmem hz, mem_univ _⟩)).contDiffOn
  exact ((contDiffOn_const.mul (contDiffOn_fst.pow 2)).mul hR).add
    (contDiffOn_const.mul hg)

theorem hasDerivAt_variationLLength_integral {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    {p : BackwardTimePath F T τ₁ τ₂} (V : LVariation F T τ₁ τ₂ p)
    {u : ℝ} (hu : u ∈ V.parameterDomain) :
    HasDerivAt (variationLLength V)
      (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
        variationParameterDeriv (sqrtParameterInterval τ₁ τ₂) V.parameterDomain
          (variationActionDensity V) (s, u)) u := by
  have h := hasDerivAt_variationIntegral (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
    isOpen_Ioo (variationActionDensity V) (variationActionDensity_contDiffOn hM04 V) hu
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
  exact variationLLength_eq_squareAction V hv

theorem hasDerivAt_deriv_variationLLength_integral {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    {p : BackwardTimePath F T τ₁ τ₂} (V : LVariation F T τ₁ τ₂ p)
    {u : ℝ} (hu : u ∈ V.parameterDomain) :
    HasDerivAt (fun v ↦ deriv (variationLLength V) v)
      (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
        variationParameterDeriv (sqrtParameterInterval τ₁ τ₂) V.parameterDomain
          (variationParameterDeriv (sqrtParameterInterval τ₁ τ₂) V.parameterDomain
            (variationActionDensity V)) (s, u)) u := by
  have hC : UniqueDiffOn ℝ (sqrtParameterInterval τ₁ τ₂) :=
    uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
  have hd := hasDerivAt_variationIntegral (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
    isOpen_Ioo (variationParameterDeriv (sqrtParameterInterval τ₁ τ₂) V.parameterDomain
      (variationActionDensity V))
    (variationParameterDeriv_contDiffOn hC isOpen_Ioo _
      (variationActionDensity_contDiffOn hM04 V)) hu
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
  exact (hasDerivAt_variationLLength_integral hM04 V hv).deriv

def variationBoundaryPair {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (s : ℝ) : ℝ :=
  (F.metric (T - s ^ 2)).inner (V.baseSquareCurve s)
    (curveVelocityWithin (n := n) V.baseSquareCurve (sqrtParameterInterval τ₁ τ₂) s)
    (squareVariationField V s)

set_option maxHeartbeats 1000000 in
theorem variationBoundaryPair_contDiffOn {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) :
    ContDiffOn ℝ ∞ (variationBoundaryPair V) (sqrtParameterInterval τ₁ τ₂) := by
  let C := sqrtParameterInterval τ₁ τ₂
  let U := (fun s : ℝ ↦ (s, (0 : ℝ))) ⁻¹' V.squareDomain
  have hU : IsOpen U := V.square_open.preimage (continuous_id.prodMk continuous_const)
  have hCU : C ⊆ U := fun s hs ↦
    V.square_contains ⟨hs, neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ V.baseSquareCurve U :=
    V.square_smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun s hs ↦ hs)
  have hA : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (V.baseSquareCurve s)
        (curveVelocityWithin (n := n) V.baseSquareCurve C s)) C := by
    apply ((contMDiffOn_mfderiv_const_apply hU V.baseSquareCurve hα (1 : ℝ)).mono hCU).congr
    intro s hs
    apply congrArg (fun w : TangentSpace (𝓡 n) (V.baseSquareCurve s) ↦
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (V.baseSquareCurve s) w)
    unfold curveVelocityWithin
    rw [mfderivWithin_eq_mfderiv (hC.uniqueMDiffOn s hs)
      (((hα s (hCU hs)).contMDiffAt (hU.mem_nhds (hCU hs))).mdifferentiableAt (by simp))]
  have ht : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun s : ℝ ↦ T - s ^ 2) C :=
    (contDiff_const.sub (contDiff_id.pow 2)).contMDiff.contMDiffOn
  have hmem : MapsTo (fun s : ℝ ↦ T - s ^ 2) C J := by
    intro s hs
    apply p.time_mem
    have hs0 : 0 ≤ s := (Real.sqrt_nonneg τ₁).trans hs.1
    constructor
    · nlinarith [Real.sq_sqrt p.nonnegative, Real.sqrt_nonneg τ₁, hs.1]
    · nlinarith [Real.sq_sqrt (p.nonnegative.trans p.ordered.le), Real.sqrt_nonneg τ₂, hs.2]
  exact (movingMetric_pair_contMDiffOn F (fun s : ℝ ↦ T - s ^ 2) V.baseSquareCurve
    (curveVelocityWithin (n := n) V.baseSquareCurve C) (squareVariationField V)
    ht (hα.mono hCU) hA ((squareVariationField_contMDiffOn V).mono hCU) hmem).contDiffOn

end PoincareConjecture.M08
