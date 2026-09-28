import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceScalarRealization
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceMetricJetBounds
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceChartMetric
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceCompactChart
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceIsometryGerm
import PoincareConjecture.Proofs.M13.Metric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

open M34

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem exists_capPersistence_chart_jet_bound (n : ℕ)
    (hn : n + 1 ≤ Nat.floor N.epsilon⁻¹) (a : M) {H : Set E₃}
    (hH : IsCompact H) (hHt : H ⊆ (extChartAt (𝓡 3) a).target) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (q : UnitTwoSphere) (s : ℝ),
      s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      N.coordinate_map (q, s) ∈ (extChartAt (𝓡 3) a).source →
      (extChartAt (𝓡 3) a) (N.coordinate_map (q, s)) ∈ H →
      ∀ j ≤ n + 2, ‖iteratedFDeriv ℝ j
        ((extChartAt (𝓡 3) a) ∘ N.capPersistenceEuclideanMap q s) 0‖ ≤ D := by
  let c := extChartAt (𝓡 3) a
  let gN : RiemannianMetric 3 M := M13.scaleSmoothMetric g (N.scale⁻¹ ^ 2)
    (sq_pos_of_pos (inv_pos.mpr N.scale_pos))
  let B := gN.pullbackCoefficients c.symm
  obtain ⟨b, hb, KB, hKB, hBbound⟩ :=
    gN.capPersistence_exists_compact_chart_bounds a hH hHt (n + 1)
  obtain ⟨KA, hKA, hAbound⟩ :=
    capPersistence_exists_realized_metric_jet_bound (n + 1) N.epsilon
  let alpha := min (1 / 2 : ℝ) b
  have halpha : 0 < alpha := lt_min (by norm_num) hb
  let K := max KA KB
  have hK : 1 ≤ K := hKA.trans (le_max_left _ _)
  obtain ⟨D, hD, hDbound⟩ :=
    CoordinateTransition.exists_local_isometry_germ_jet_bound (E := E₃) n halpha hK
  refine ⟨D, hD, ?_⟩
  intro q s hs hsource hcenter j hj
  let φ := N.capPersistenceEuclideanMap q s
  let f := c ∘ φ
  have hφ0 : φ 0 = N.coordinate_map (q, s) :=
    congrArg N.coordinate_map (capPersistenceSphereChart_zero q s)
  have hf0 : f 0 = c (N.coordinate_map (q, s)) := congrArg c hφ0
  obtain ⟨gE, _DE, V, hV, h0V, haxis, hcoeff, _hscalar⟩ :=
    N.exists_capPersistence_metric_germ q s hs
  let A := gE.euclideanCoefficients
  have hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ V := fun x hx =>
    (N.capPersistenceEuclideanMap_contMDiffAt q s (haxis x hx)).contMDiffWithinAt
  let U := V ∩ φ ⁻¹' c.source
  have hU : IsOpen U := hφ.continuousOn.isOpen_inter_preimage hV
    (isOpen_extChartAt_source a)
  have h0U : (0 : E₃) ∈ U := ⟨h0V, by
    change φ 0 ∈ c.source
    rw [hφ0]
    exact hsource⟩
  have hmap : MapsTo f U c.target := fun x hx => c.map_source hx.2
  have hf : ContDiffOn ℝ ∞ f U := by
    intro x hx
    apply (contMDiffAt_iff_contDiffAt.mp ?_).contDiffWithinAt
    exact ((contMDiffOn_extChartAt (I := 𝓡 3) (x := a) (n := ∞)).contMDiffAt
      (by simpa only [extChartAt_source] using
        (isOpen_extChartAt_source a).mem_nhds hx.2)).comp x
        (N.capPersistenceEuclideanMap_contMDiffAt q s (haxis x hx.1))
  have hmetric (x : E₃) (hx : x ∈ U) (v w : E₃) :
      A x v w = B (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) := by
    have he := gN.capPersistence_chart_pullback a
      ((N.capPersistenceEuclideanMap_contMDiffAt q s (haxis x hx.1)).mdifferentiableAt
        (by simp)) hx.2
    calc
      A x v w = N.scale⁻¹ ^ 2 * g.pullbackCoefficients φ x v w :=
        congrArg (fun L : E₃ →L[ℝ] E₃ →L[ℝ] ℝ => L v w) (hcoeff x hx.1)
      _ = gN.pullbackCoefficients φ x v w := rfl
      _ = _ := (congrArg (fun L : E₃ →L[ℝ] E₃ →L[ℝ] ℝ => L v w) he).symm
  have hAj : ∀ l ≤ n + 1, ‖iteratedFDeriv ℝ l A 0‖ ≤ KA := by
    apply hAbound
      (fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w)
      N.metric_comparison.close hn q s hs gE
    intro i l
    filter_upwards [hV.mem_nhds h0V] with x hx
    exact (congrArg (fun L : E₃ →L[ℝ] E₃ →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ l)) (hcoeff x hx)).trans
      (N.capPersistenceEuclideanMap_coefficient q s (haxis x hx) i l)
  have hAcoerce (v : E₃) : alpha * ‖v‖ ^ 2 ≤ A 0 v v := by
    calc
      _ ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
      _ ≤ N.scale⁻¹ ^ 2 * g.pullbackCoefficients φ 0 v v :=
        N.capPersistenceEuclideanMap_origin_lower q s hs v
      _ = A 0 v v :=
        (congrArg (fun L : E₃ →L[ℝ] E₃ →L[ℝ] ℝ => L v v) (hcoeff 0 h0V)).symm
  have hcenter' : f 0 ∈ H := by rw [hf0]; exact hcenter
  apply hDbound A B f U c.target 0 hU (isOpen_extChartAt_target a) h0U
    (fun x _ => (gE.contDiffAt_euclideanCoefficients x).contDiffWithinAt)
    (gN.contDiffOn_chartCoefficients a) hf
    (fun x _ => gE.inner_isInvertible x)
    (fun _ hx => gN.isInvertible_chartCoefficients a hx)
    (fun y _ v w => gN.symm _ _ _) hmap hmetric
    ((hBbound _ hcenter').1.trans (le_max_right _ _))
    (fun l hl => (hAj l hl).trans (le_max_left _ _))
    (fun l hl => ((hBbound _ hcenter').2.1 l hl).trans (le_max_right _ _))
    hAcoerce (fun v => ?_) j hj
  exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans
    ((hBbound _ hcenter').2.2 v)

end PoincareConjecture.EpsilonNeck
