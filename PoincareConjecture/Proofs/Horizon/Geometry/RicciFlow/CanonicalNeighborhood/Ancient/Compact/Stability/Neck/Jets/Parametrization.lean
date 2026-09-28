import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.Jets.MetricIsometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.Covariant
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactEnergy

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.MetricSurgery

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem normalizedNeckMetric_centeredCoefficients_lower
    (N : EpsilonNeck g) (hsmall : N.epsilon < 1 / 200)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : E₃) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
      (normalizedNeckMetric N).parametrizedCoefficients (centeredNeckLift N z.1 z.2)
        0 v v := by
  rw [normalizedNeckMetric_centeredCoefficients_eq_model_add_error N z.1 z.2
    (zero_mem_centeredNeckDomain N hz)]
  simp only [add_apply]
  let F := centeredCylinderError (fun z v w => normalizedNeckForm N z v w) z.1 z.2 0
  have hb : ‖F‖ ≤ 18 * N.epsilon :=
    (roundCylinderClose_error_operator_bounds N.epsilon_pos N.metric_comparison.close
      N.two_le_floor_inv_epsilon z hz).1
  have he : |F v v| ≤ (18 * N.epsilon) * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖F‖ * ‖v‖ * ‖v‖ := F.le_opNorm₂ v v
      _ ≤ (18 * N.epsilon) * ‖v‖ ^ 2 := by
        simpa only [pow_two, mul_assoc] using
          mul_le_mul_of_nonneg_right hb (mul_nonneg (norm_nonneg v) (norm_nonneg v))
  have hlower := cylinderModelField_zero_lower v
  have hnonneg : 0 ≤ (1 / 2 - 18 * N.epsilon) * ‖v‖ ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have he' := (abs_le.mp he).1
  change (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ cylinderModelField 0 v v + F v v
  nlinarith

def centeredNeckAmbientDomain (N : EpsilonNeck g) (q : M) (z : RoundCylinderSpace) :
    Set E₃ :=
  centeredNeckDomain N z.2 ∩
    centeredNeckLift N z.1 z.2 ⁻¹' (extChartAt (𝓡 3) q).source

def centeredNeckAmbientCoordinates (N : EpsilonNeck g) (q : M) (z : RoundCylinderSpace) :
    E₃ → E₃ :=
  extChartAt (𝓡 3) q ∘ centeredNeckLift N z.1 z.2

theorem centeredNeckAmbientDomain_isOpen
    (N : EpsilonNeck g) (q : M) (z : RoundCylinderSpace) :
    IsOpen (centeredNeckAmbientDomain N q z) := by
  apply ContinuousOn.isOpen_inter_preimage
    (fun p hp => (centeredNeckLift_contMDiffAt N z.1 z.2 hp).continuousAt.continuousWithinAt)
    (centeredNeckDomain_isOpen N z.2)
  simpa only [extChartAt_source] using (chartAt E₃ q).open_source

theorem zero_mem_centeredNeckAmbientDomain
    (N : EpsilonNeck g) (q : M) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hq : N.coordinate_map z ∈ (extChartAt (𝓡 3) q).source) :
    0 ∈ centeredNeckAmbientDomain N q z := by
  refine ⟨zero_mem_centeredNeckDomain N hz, ?_⟩
  simpa only [mem_preimage, centeredNeckLift_zero] using hq

@[simp] theorem centeredNeckAmbientCoordinates_zero
    (N : EpsilonNeck g) (q : M) (z : RoundCylinderSpace) :
    centeredNeckAmbientCoordinates N q z 0 = extChartAt (𝓡 3) q (N.coordinate_map z) := by
  simp only [centeredNeckAmbientCoordinates, Function.comp_apply, centeredNeckLift_zero]

theorem centeredNeckAmbientCoordinates_contDiffAt
    (N : EpsilonNeck g) (q : M) (z : RoundCylinderSpace)
    {p : E₃} (hp : p ∈ centeredNeckAmbientDomain N q z) :
    ContDiffAt ℝ ∞ (centeredNeckAmbientCoordinates N q z) p := by
  apply contMDiffAt_iff_contDiffAt.mp
  exact (contMDiffAt_extChartAt' (by simpa only [extChartAt_source, mem_preimage]
    using hp.2)).comp p
    (centeredNeckLift_contMDiffAt N z.1 z.2 hp.1)

theorem centeredNeckAmbientCoordinates_mem_target
    (N : EpsilonNeck g) (q : M) (z : RoundCylinderSpace)
    {p : E₃} (hp : p ∈ centeredNeckAmbientDomain N q z) :
    centeredNeckAmbientCoordinates N q z p ∈ (extChartAt (𝓡 3) q).target :=
  (extChartAt (𝓡 3) q).map_source hp.2

theorem centeredNeckAmbientCoordinates_metric
    (N : EpsilonNeck g) (q : M) (z : RoundCylinderSpace)
    {p : E₃} (hp : p ∈ centeredNeckAmbientDomain N q z) (v w : E₃) :
    (normalizedNeckMetric N).parametrizedCoefficients
        (centeredNeckLift N z.1 z.2) p v w =
      (normalizedNeckMetric N).parametrizedCoefficients (extChartAt (𝓡 3) q).symm
        (centeredNeckAmbientCoordinates N q z p)
        (fderiv ℝ (centeredNeckAmbientCoordinates N q z) p v)
        (fderiv ℝ (centeredNeckAmbientCoordinates N q z) p w) := by
  have ht := centeredNeckAmbientCoordinates_mem_target N q z hp
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds ht)
  have heq : (extChartAt (𝓡 3) q).symm ∘ centeredNeckAmbientCoordinates N q z
      =ᶠ[𝓝 p] centeredNeckLift N z.1 z.2 := by
    filter_upwards [(centeredNeckAmbientDomain_isOpen N q z).mem_nhds hp] with y hy
    exact (extChartAt (𝓡 3) q).left_inv hy.2
  exact (congrArg (fun B : E₃ →L[ℝ] E₃ →L[ℝ] ℝ => B v w)
    ((normalizedNeckMetric N).parametrizedCoefficients_comp_of_eventuallyEq
      (hi.mdifferentiableAt (by simp))
      ((centeredNeckAmbientCoordinates_contDiffAt N q z hp).differentiableAt (by simp))
      heq)).symm

theorem exists_centeredNeckAmbientCoordinates_jet_bound
    (N : EpsilonNeck g) (hsmall : N.epsilon < 1 / 200) (q : M)
    {K : Set M} (hK : IsCompact K) (hKq : K ⊆ (extChartAt (𝓡 3) q).source)
    (r : ℕ) (hr : 1 ≤ r) (horder : r ≤ ⌊N.epsilon⁻¹⌋₊) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        N.coordinate_map z ∈ K →
        ∀ j : ℕ, j ≤ r + 1 →
          ‖iteratedFDeriv ℝ j (centeredNeckAmbientCoordinates N q z) 0‖ ≤ C := by
  let c := extChartAt (𝓡 3) q
  let gN := normalizedNeckMetric N
  let T : Set E₃ := c '' K
  have hT : IsCompact T :=
    hK.image_of_continuousOn ((continuousOn_extChartAt q).mono hKq)
  have hTq : T ⊆ c.target := by
    rintro y ⟨p, hp, rfl⟩
    exact c.map_source (hKq hp)
  let B₀ := gN.parametrizedCoefficients c.symm
  have hBs (y : E₃) (hy : y ∈ c.target) : ContDiffAt ℝ ∞ B₀ y :=
    gN.contDiffAt_parametrizedCoefficients
      ((contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) q).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hy))
  have hBpos (y : E₃) (hy : y ∈ T) (v : E₃) (hv : v ≠ 0) : 0 < B₀ y v v := by
    change 0 < gN.inner (c.symm y) (mfderiv (𝓡 3) (𝓡 3) c.symm y v)
      (mfderiv (𝓡 3) (𝓡 3) c.symm y v)
    apply gN.pos
    intro hz
    apply hv
    apply (gN.isInvertible_chartCoefficients q (hTq hy)).injective
    ext w
    change gN.inner (c.symm y) (mfderiv (𝓡 3) (𝓡 3) c.symm y v)
      (mfderiv (𝓡 3) (𝓡 3) c.symm y w) =
      gN.inner (c.symm y) (mfderiv (𝓡 3) (𝓡 3) c.symm y 0)
        (mfderiv (𝓡 3) (𝓡 3) c.symm y w)
    simp only [hz, map_zero]
  obtain ⟨b, hb, hBlower⟩ := exists_uniform_bilinear_lower_bound hT
    (fun y hy => (hBs y (hTq hy)).continuousAt.continuousWithinAt) hBpos
  obtain ⟨CB, _, hCB⟩ := exists_compact_local_jet_bound hT
    (fun y hy => hBs y (hTq hy)) r
  obtain ⟨CA, _, hCA⟩ := exists_normalizedNeck_centered_coefficient_jet_bounds.{u} r
  obtain ⟨C₀, hC₀⟩ := hT.exists_bound_of_continuousOn continuousOn_id
  let Z := {z : RoundCylinderSpace //
    z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ ∧ N.coordinate_map z ∈ K}
  let f := fun z : Z => centeredNeckAmbientCoordinates N q z
  let A := fun z : Z => gN.parametrizedCoefficients (centeredNeckLift N z.1.1 z.1.2)
  let B := fun _z : Z => B₀
  have hmem (z : Z) : 0 ∈ centeredNeckAmbientDomain N q z :=
    zero_mem_centeredNeckAmbientDomain N q z z.2.1 (hKq z.2.2)
  have hmap (z : Z) : f z 0 ∈ T := by
    change centeredNeckAmbientCoordinates N q z 0 ∈ T
    rw [centeredNeckAmbientCoordinates_zero]
    exact mem_image_of_mem c z.2.2
  have hf (z : Z) : ∀ᶠ y in 𝓝 (0 : E₃), ContDiffAt ℝ ∞ (f z) y := by
    filter_upwards [(centeredNeckAmbientDomain_isOpen N q z).mem_nhds (hmem z)] with y hy
    exact centeredNeckAmbientCoordinates_contDiffAt N q z hy
  have hA (z : Z) : ∀ᶠ y in 𝓝 (0 : E₃), ContDiffAt ℝ ∞ (A z) y := by
    filter_upwards [(centeredNeckDomain_isOpen N z.1.2).mem_nhds
      (zero_mem_centeredNeckDomain N z.2.1)] with y hy
    exact gN.contDiffAt_parametrizedCoefficients (centeredNeckLift_contMDiffAt N z.1.1 z.1.2 hy)
  have hB (z : Z) : ∀ᶠ y in 𝓝 (f z 0), ContDiffAt ℝ ∞ (B z) y := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds
      (hTq (hmap z))] with y hy
    exact hBs y hy
  have hsymm (z : Z) : ∀ᶠ y in 𝓝 (f z 0), ∀ v w, B z y v w = B z y w v :=
    Eventually.of_forall fun y v w => gN.symm (c.symm y) _ _
  have hmetric (z : Z) : ∀ᶠ y in 𝓝 (0 : E₃), ∀ v w,
      A z y v w = B z (f z y) (fderiv ℝ (f z) y v) (fderiv ℝ (f z) y w) := by
    filter_upwards [(centeredNeckAmbientDomain_isOpen N q z).mem_nhds (hmem z)] with y hy
    exact centeredNeckAmbientCoordinates_metric N q z hy
  obtain ⟨C, hC, hbound⟩ := CoordinateTransition.exists_finite_metric_isometry_jet_bound_at
    (A := A) (B := B) (f := f) (fun _z : Z => (0 : E₃)) hf hA hB r hr
    ⟨CA, fun z j hj => hCA N j hj (hj.trans horder) z z.2.1⟩
    ⟨CB, fun z j hj => hCB j hj (f z 0) (hmap z)⟩
    (by norm_num : (0 : ℝ) < 1 / 2) hb
    (fun z v => normalizedNeckMetric_centeredCoefficients_lower N hsmall z z.2.1 v)
    (fun z v => hBlower (f z 0) (hmap z) v)
    ⟨C₀, fun z => hC₀ (f z 0) (hmap z)⟩ hsymm hmetric
  exact ⟨C, hC, fun z hz hKz j hj => hbound ⟨z, hz, hKz⟩ j hj⟩

end PoincareConjecture.MetricSurgery
