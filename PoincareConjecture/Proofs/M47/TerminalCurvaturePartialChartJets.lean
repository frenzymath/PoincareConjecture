import PoincareConjecture.Proofs.M47.TerminalCurvaturePartialChartMetric
import PoincareConjecture.Proofs.M47.TerminalCurvatureMovingJetBounds
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceScalarRealization
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceMetricJetBounds
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceChartMetric
import PoincareConjecture.Proofs.M13.Metric










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open M34

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalCurvature_exists_neck_partial_chart_jet_bound_uniform
    {epsilon : ℝ} (m : ℕ) (hm : m + 1 ≤ Nat.floor epsilon⁻¹)
    {b K : ℝ} (hb : 0 < b) (hK : 1 ≤ K) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
      [IsManifold (𝓡 3) ∞ M] [T2Space M] (g : RiemannianMetric 3 M) (N : EpsilonNeck g),
      N.epsilon = epsilon →
      ∀ (c : PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞)
        (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      N.coordinate_map (q, s) ∈ c.source →
      let B := RiemannianMetric.pullbackCoefficients
        (M13.scaleSmoothMetric g (N.scale⁻¹ ^ 2)
          (sq_pos_of_pos (inv_pos.mpr N.scale_pos))) c.symm
      ‖c (N.coordinate_map (q, s))‖ ≤ K →
      (∀ j ≤ m + 1, ‖iteratedFDeriv ℝ j B (c (N.coordinate_map (q, s)))‖ ≤ K) →
      (∀ v, b * ‖v‖ ^ 2 ≤ B (c (N.coordinate_map (q, s))) v v) →
      ∀ j ≤ m + 2, ‖iteratedFDeriv ℝ j
        ((c : M → E) ∘ N.capPersistenceEuclideanMap q s) 0‖ ≤ D := by
  obtain ⟨KA, hKA, hAbound⟩ := capPersistence_exists_realized_metric_jet_bound (m + 1) epsilon
  let alpha := min (1 / 2 : ℝ) b
  have halpha : 0 < alpha := lt_min (by norm_num) hb
  let K0 := max KA K
  have hK0 : 1 ≤ K0 := (le_max_left (1 : ℝ) 1).trans (max_le_max hKA hK)
  obtain ⟨D, hD, hDbound⟩ := terminalCurvature_exists_moving_isometry_jet_bound m halpha hK0
  refine ⟨D, hD, ?_⟩
  intro M _ _ _ _ g N hN c q s hs hsource B hcenter hBj hBcoerce j hj
  have hsN : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by simpa only [hN] using hs
  let gN : RiemannianMetric 3 M := M13.scaleSmoothMetric g (N.scale⁻¹ ^ 2)
    (sq_pos_of_pos (inv_pos.mpr N.scale_pos))
  let phi := N.capPersistenceEuclideanMap q s
  let f := (c : M → E) ∘ phi
  have hphi0 : phi 0 = N.coordinate_map (q, s) :=
    congrArg N.coordinate_map (capPersistenceSphereChart_zero q s)
  have hf0 : f 0 = c (N.coordinate_map (q, s)) := congrArg c hphi0
  obtain ⟨gE, _DE, V, hV, h0V, haxis, hcoeff, _hscalar⟩ :=
    N.exists_capPersistence_metric_germ q s hsN
  let A := gE.euclideanCoefficients
  have hphi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ phi V := fun x hx =>
    (N.capPersistenceEuclideanMap_contMDiffAt q s (haxis x hx)).contMDiffWithinAt
  let U := V ∩ phi ⁻¹' c.source
  have hU : IsOpen U := hphi.continuousOn.isOpen_inter_preimage hV c.open_source
  have h0U : (0 : E) ∈ U := ⟨h0V, by
    change phi 0 ∈ c.source
    rw [hphi0]
    exact hsource⟩
  have hmap : MapsTo f U c.target := fun x hx => c.map_source hx.2
  have hf : ContDiffOn ℝ ∞ f U := by
    intro x hx
    apply (contMDiffAt_iff_contDiffAt.mp ?_).contDiffWithinAt
    exact (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hx.2)).comp x
      (N.capPersistenceEuclideanMap_contMDiffAt q s (haxis x hx.1))
  have hmetric (x : E) (hx : x ∈ U) (v w : E) :
      A x v w = B (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) := by
    have he := terminalCurvature_partial_chart_metric gN c
      ((N.capPersistenceEuclideanMap_contMDiffAt q s (haxis x hx.1)).mdifferentiableAt
        (by simp)) hx.2
    calc
      A x v w = N.scale⁻¹ ^ 2 * g.pullbackCoefficients phi x v w :=
        congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L v w) (hcoeff x hx.1)
      _ = gN.pullbackCoefficients phi x v w := rfl
      _ = _ := (congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L v w) he).symm
  have hAj : ∀ l ≤ m + 1, ‖iteratedFDeriv ℝ l A 0‖ ≤ KA := by
    apply hAbound
      (fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w)
      (by simpa only [hN] using N.metric_comparison.close) hm q s hs gE
    intro i l
    filter_upwards [hV.mem_nhds h0V] with x hx
    exact (congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ l)) (hcoeff x hx)).trans
      (N.capPersistenceEuclideanMap_coefficient q s (haxis x hx) i l)
  have hAcoerce (v : E) : alpha * ‖v‖ ^ 2 ≤ A 0 v v := by
    calc
      _ ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
      _ ≤ N.scale⁻¹ ^ 2 * g.pullbackCoefficients phi 0 v v :=
        N.capPersistenceEuclideanMap_origin_lower q s hsN v
      _ = A 0 v v :=
        (congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L v v) (hcoeff 0 h0V)).symm
  have hBactual := terminalCurvature_partial_chart_coefficients gN c
  apply hDbound A B f U c.target 0 hU c.open_target h0U
    (fun x _ => (gE.contDiffAt_euclideanCoefficients x).contDiffWithinAt)
    hBactual.1 hf (fun x _ => gE.inner_isInvertible x) hBactual.2
    (fun y _ v w => gN.symm _ _ _) hmap hmetric
    (by rw [hf0]; exact hcenter.trans (le_max_right _ _))
    (fun l hl => (hAj l hl).trans (le_max_left _ _))
    (fun l hl => by rw [hf0]; exact (hBj l hl).trans (le_max_right _ _)) hAcoerce
    (fun v => ?_) j hj
  rw [hf0]
  exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans (hBcoerce v)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]



theorem terminalCurvature_exists_neck_partial_chart_jet_bound
    {epsilon : ℝ} (m : ℕ) (hm : m + 1 ≤ Nat.floor epsilon⁻¹)
    {b K : ℝ} (hb : 0 < b) (hK : 1 ≤ K) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (g : RiemannianMetric 3 M) (N : EpsilonNeck g),
      N.epsilon = epsilon →
      ∀ (c : PartialDiffeomorph (𝓡 3) (𝓡 3) M E ∞)
        (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      N.coordinate_map (q, s) ∈ c.source →
      let B := RiemannianMetric.pullbackCoefficients
        (M13.scaleSmoothMetric g (N.scale⁻¹ ^ 2)
          (sq_pos_of_pos (inv_pos.mpr N.scale_pos))) c.symm
      ‖c (N.coordinate_map (q, s))‖ ≤ K →
      (∀ j ≤ m + 1, ‖iteratedFDeriv ℝ j B (c (N.coordinate_map (q, s)))‖ ≤ K) →
      (∀ v, b * ‖v‖ ^ 2 ≤ B (c (N.coordinate_map (q, s))) v v) →
      ∀ j ≤ m + 2, ‖iteratedFDeriv ℝ j
        ((c : M → E) ∘ N.capPersistenceEuclideanMap q s) 0‖ ≤ D := by
  obtain ⟨D, hD, hbound⟩ :=
    terminalCurvature_exists_neck_partial_chart_jet_bound_uniform m hm hb hK
  exact ⟨D, hD, hbound M⟩

end PoincareConjecture.M47
