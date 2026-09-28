import PoincareConjecture.Proofs.M47.BlowupControlsCapNeckError










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open SpacetimeBounds Proofs.M46

local notation "E" => StandardCapSpace
local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

noncomputable local instance sourceNeckCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance sourceNeckCoefficientSpace : NormedSpace ℝ (MetricCoefficient 3) :=
  ContinuousLinearMap.toNormedSpace

private theorem source_neck_image_coefficient_difference
    {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsManifold (𝓡 3) ∞ X] {g0 : RiemannianMetric 3 E} (N : EpsilonNeck g0)
    (g : RiemannianMetric 3 E) (h : RiemannianMetric 3 X)
    {f : E → X} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) (hNU : N.carrier ⊆ U)
    (A : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hA : ∀ x ∈ U, ∀ v w : E,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x w) = A x v w)
    (q : UnitTwoSphere) {y : RoundCylinderCoordinates}
    (hy : y.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (i l : Fin 3) :
    roundCylinderTensorCoefficient (roundCylinderPullback h (f ∘ N.coordinate_map))
        (chartAt E₂ q) y i l -
      roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate_map)
        (chartAt E₂ q) y i l =
      roundCylinderTensorCoefficient
        (fun z v w => (A (N.coordinate_map z) - g.euclideanCoefficients (N.coordinate_map z))
          (mfderiv Ic (𝓡 3) N.coordinate_map z v)
          (mfderiv Ic (𝓡 3) N.coordinate_map z w)) (chartAt E₂ q) y i l := by
  let z : RoundCylinderSpace := ((chartAt E₂ q).symm y.1, y.2)
  have hx := hNU (N.coordinate_map_mem_of_axial_mem (z := z) hy)
  have hcoord := (N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show z ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from
        ⟨mem_univ _, hy⟩))).mdifferentiableAt (by simp)
  have htarget := (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hdiff (v w : RoundCylinderTangent z) :
      roundCylinderPullback h (f ∘ N.coordinate_map) z v w -
        roundCylinderPullback g N.coordinate_map z v w =
        (A (N.coordinate_map z) - g.euclideanCoefficients (N.coordinate_map z))
          (mfderiv Ic (𝓡 3) N.coordinate_map z v)
          (mfderiv Ic (𝓡 3) N.coordinate_map z w) := by
    unfold roundCylinderPullback
    rw [mfderiv_comp z htarget hcoord]
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, sub_apply]
    rw [hA _ hx]
    rfl
  exact hdiff _ _



theorem exists_actualCap_fixed_neck_coefficient_error_bound
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    {theta A v L : ℝ} (htheta : theta < 1) (hA : 0 < A) (hL : 0 < L)
    (N : EpsilonNeck (standard.flow.metric v))
    (hsource : N.carrier ⊆ g0.metric.ball 0 A)
    (m : ℕ) (hm : m ≤ Nat.floor N.epsilon⁻¹) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial), HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ 1 / ((m : ℝ) + 1) →
      ∀ (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
        (hh : 0 < F.parameters.h t) (s : ℝ) (hs : s ∈ J), s ≤ theta →
      ∀ rho : ℝ, 0 < rho → rho ≤ L →
      let phi := actualCapSliceChart e initial comparison s hs
      let Q := (F.parameters.h t)⁻¹ ^ 2
      let g' := m01RescaledMetric (F.metric (t + s / Q)) Q
        (sq_pos_of_pos (inv_pos.mpr hh))
      ∀ (q : UnitTwoSphere) (z : ℝ), z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j ≤ m, ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          rho * roundCylinderTensorCoefficient
            (roundCylinderPullback g' (phi ∘ N.coordinate_map)) (chartAt E₂ q) y a b -
          rho * roundCylinderTensorCoefficient
            (roundCylinderPullback (standard.flow.metric s) N.coordinate_map)
            (chartAt E₂ q) y a b) (0, z)‖ ≤ C * eta := by
  have hNK : N.carrier ⊆ {x : E | g0.metric.edist 0 x ≤ ENNReal.ofReal A} := by
    intro x hx
    exact (show g0.metric.edist 0 x < ENNReal.ofReal A from hsource hx).le
  obtain ⟨C0, hC0, hnative⟩ := exists_cap_neck_bilinear_error_jet_bound N m hm
    (M36.standard_closed_ball_compact g0 hA.le) hNK
  obtain ⟨C1, hC1, hambient⟩ :=
    exists_actualCap_coordinate_derivative_bound standard htheta hA m
  refine ⟨C0 * (L * C1), mul_pos hC0 (mul_pos hL hC1), ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta hetaOrder comparison hh s hs hst
    rho hrho hrhoL
  have hambient' := hambient F hinitial S hS t hT hn i J U e initial eta heta hetaOrder
    comparison s hs hst
  cases hinitial
  cases hS
  let V := F.standard_initial.metric.ball 0 A
  have hV : IsOpen V := (capInitialPartialDiffeomorph initial).open_source
  have himage : initial.chart '' V = U := comparison.choose_spec.2.2.2.1
  have hU : IsOpen U := himage ▸ (capInitialPartialDiffeomorph initial).open_target
  have hmap : MapsTo initial.chart V U := fun _ hx => himage ▸ mem_image_of_mem initial.chart hx
  let phi := actualCapSliceChart e initial comparison s hs
  let Q := (F.parameters.h t)⁻¹ ^ 2
  let g' := m01RescaledMetric (F.metric (t + s / Q)) Q (sq_pos_of_pos (inv_pos.mpr hh))
  let coeff := capComparisonCoefficients e initial.chart s hs
  let T : E → E →L[ℝ] E →L[ℝ] ℝ :=
    fun x => rho • (coeff x - (standard.flow.metric s).euclideanCoefficients x)
  have hcoeff := capComparisonCoefficients_smooth e hU hV initial.chart_smooth hmap s hs
  have hT (x : E) (hx : x ∈ N.carrier) : ContDiffAt ℝ ∞ T x :=
    ((hcoeff.contDiffAt (hV.mem_nhds (hsource hx))).sub
      ((standard.flow.metric s).contDiffAt_euclideanCoefficients x)).const_smul rho
  have hTjet (x : E) (hx : x ∈ N.carrier) (j : ℕ) (hj : j ≤ m) :
      ‖iteratedFDeriv ℝ j T x‖ ≤ (L * C1) * eta := by
    have hnew := hcoeff.contDiffAt (hV.mem_nhds (hsource hx))
    have hold := (standard.flow.metric s).contDiffAt_euclideanCoefficients x
    change ‖iteratedFDeriv ℝ j
      (fun x => rho • (coeff x - (standard.flow.metric s).euclideanCoefficients x)) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' ((hnew.sub hold).of_le
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)), norm_smul, Real.norm_eq_abs,
      abs_of_pos hrho, fun_iteratedFDeriv_sub_apply
        (hnew.of_le (by exact_mod_cast le_top)) (hold.of_le (by exact_mod_cast le_top))]
    exact (mul_le_mul hrhoL (hambient' x (hsource hx) j hj)
      (norm_nonneg _) hL.le).trans_eq (by ring)
  have hphismooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ phi V := by
    simpa only [phi, actualCapSliceChart_source] using
      (actualCapSliceChart e initial comparison s hs).contMDiffOn_toFun
  have hmetric (x : E) (hx : x ∈ V) (w w' : E) :
      g'.inner (phi x) (mfderiv (𝓡 3) (𝓡 3) phi x w)
        (mfderiv (𝓡 3) (𝓡 3) phi x w') = coeff x w w' :=
    actualCapSliceChart_metric e initial comparison s hs hh hx w w'
  dsimp only
  intro q z hz j hj a b
  let tensor : RoundCylinderTwoTensor := fun w u u' => T (N.coordinate_map w)
    (mfderiv Ic (𝓡 3) N.coordinate_map w u) (mfderiv Ic (𝓡 3) N.coordinate_map w u')
  have hbound := hnative T hT ((L * C1) * eta)
    (mul_nonneg (mul_nonneg hL.le hC1.le) heta.le) hTjet q z hz j hj a b
  have heq : (fun y =>
      rho * roundCylinderTensorCoefficient (roundCylinderPullback g'
        (phi ∘ N.coordinate_map)) (chartAt E₂ q) y a b -
      rho * roundCylinderTensorCoefficient (roundCylinderPullback (standard.flow.metric s)
        N.coordinate_map) (chartAt E₂ q) y a b) =ᶠ[𝓝 (0, z)]
      (fun y => roundCylinderTensorCoefficient tensor (chartAt E₂ q) y a b) := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (0, z) ∈ (univ : Set E₂) ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from
        ⟨mem_univ _, hz⟩)] with y hy
    rw [← mul_sub, source_neck_image_coefficient_difference N
      (standard.flow.metric s) g' hV hphismooth hsource coeff hmetric q hy.2 a b]
    rfl
  rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
  exact hbound.trans_eq (by ring)

end PoincareConjecture.M47
