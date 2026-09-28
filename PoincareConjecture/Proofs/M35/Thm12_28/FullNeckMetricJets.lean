import PoincareConjecture.Proofs.M35.Thm12_28.FullNeckMetricRealization
import PoincareConjecture.Proofs.M35.Thm12_28.NeckFiniteMetricJets
import PoincareConjecture.Proofs.M35.Mathlib.PointJetBounds
import PoincareConjecture.Proofs.M35.Thm12_28.MetricConnectionJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)

theorem metric_jetsAt_of_component_jets {ι : Type*} {n : ℕ}
    (g : ι → RiemannianMetric 3 V) (p : ι → V)
    (hcomp : ∀ a b : Fin 3, HasUniformJetBoundsAt n
      (fun i y => (g i).inner y (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) p) :
    HasUniformJetBoundsAt n (fun i => (g i).euclideanCoefficients) p := by
  classical
  intro r hr
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let G := V →L[ℝ] V →L[ℝ] ℝ
  let ev (a b' : Fin 3) : G →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ (b b')).comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (b a))
  let L : (V [×r]→L[ℝ] G) →ₗ[ℝ] (Fin 3 → Fin 3 → V [×r]→L[ℝ] ℝ) :=
    LinearMap.pi fun a => LinearMap.pi fun b' =>
      (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
        (fun _ : Fin r => V) G ℝ (ev a b')).toLinearMap
  have hL : Function.Injective L := by
    intro A B hAB
    apply ContinuousMultilinearMap.ext
    intro v
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro a
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    intro b'
    exact congrArg (fun f => f a b' v) hAB
  let : FiniteDimensional ℝ (V [×r]→L[ℝ] G) :=
    FiniteDimensional.of_injective ContinuousMultilinearMap.toMultilinearMapLinear
      ContinuousMultilinearMap.toMultilinearMap_injective
  obtain ⟨K, _, hanti⟩ := L.injective_iff_antilipschitz.mp hL
  choose C hC using fun ab : Fin 3 × Fin 3 => hcomp ab.1 ab.2 r hr
  let D := ∑ ab, max (C ab) 0
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  refine ⟨K * D, fun i => ?_⟩
  apply (hanti.le_mul_norm (map_zero L)
    (iteratedFDeriv ℝ r (g i).euclideanCoefficients (p i))).trans
  apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
  apply (pi_norm_le_iff_of_nonneg hD).mpr
  intro a
  apply (pi_norm_le_iff_of_nonneg hD).mpr
  intro b'
  have heq : L (iteratedFDeriv ℝ r (g i).euclideanCoefficients (p i)) a b' =
      iteratedFDeriv ℝ r (fun y => (g i).inner y (b a) (b b')) (p i) := by
    ext v
    exact ((g i).iteratedFDeriv_inner_eq (p i) (b a) (b b') r v).symm
  rw [heq]
  exact (hC (a, b') i).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ (a, b'))))

end PoincareConjecture.M35

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

local notation "V" => EuclideanSpace ℝ (Fin 3)

theorem full_normalized_realization_jets (N : EpsilonNeck g) {ι : Type*}
    (q : ι → UnitTwoSphere) (s : ι → ℝ)
    (hs : ∀ i, s i ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (g' : ι → RiemannianMetric 3 V)
    (hmetric : ∀ i, ∀ᶠ y in 𝓝 (M35.cylinderCoordinateEquiv.symm (0, s i)),
      (g' i).euclideanCoefficients y = N.scale⁻¹ ^ 2 •
        g.pullbackCoefficients (N.coordinate_map ∘ M35.cylinderChart (q i)) y) :
    M35.HasUniformJetBoundsAt ⌊N.epsilon⁻¹⌋₊ (fun i => (g' i).euclideanCoefficients)
      (fun i => M35.cylinderCoordinateEquiv.symm (0, s i)) := by
  let p (i : ι) := M35.cylinderCoordinateEquiv.symm (0, s i)
  let K : Set RoundCylinderCoordinates := {0} ×ˢ Icc (-N.epsilon⁻¹) N.epsilon⁻¹
  have hK : IsCompact K := isCompact_singleton.prod isCompact_Icc
  have himage : IsCompact (M35.cylinderCoordinateEquiv.symm '' K) :=
    hK.image M35.cylinderCoordinateEquiv.symm.continuous
  have hp (i : ι) : p i ∈ M35.cylinderCoordinateEquiv.symm '' K :=
    ⟨(0, s i), ⟨mem_singleton _, (hs i).1.le, (hs i).2.le⟩, rfl⟩
  have hlinear : M35.HasUniformJetBoundsAt ⌊N.epsilon⁻¹⌋₊
      (fun _ : ι => M35.cylinderCoordinateEquiv) p := by
    intro r _
    obtain ⟨C, hC⟩ := himage.exists_bound_of_continuousOn
      ((M35.cylinderCoordinateEquiv.contDiff (n := ∞)).continuous_iteratedFDeriv
        (by exact_mod_cast le_top (a := (r : ℕ∞)))).continuousOn
    exact ⟨C, fun i => hC (p i) (hp i)⟩
  apply M35.metric_jetsAt_of_component_jets g' p
  intro a b
  let B := fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w
  let A (i : ι) (y : RoundCylinderCoordinates) :=
    roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) y a b
  have hA : ∀ i, ContDiffAt ℝ ∞ (A i) (M35.cylinderCoordinateEquiv (p i)) := by
    intro i
    simpa only [p, ContinuousLinearEquiv.apply_symm_apply] using
      N.metric_comparison.close.contDiffAt_coefficient (q i) (0, s i) (hs i) a b
  have hj : M35.HasUniformJetBoundsAt ⌊N.epsilon⁻¹⌋₊ A
      (fun i => M35.cylinderCoordinateEquiv (p i)) := by
    intro r hr
    obtain ⟨C, _, hC⟩ := M35.full_neck_metric_coefficient_jet_bounds
      N.metric_comparison.close N.epsilon_pos r hr
    refine ⟨C, fun i => ?_⟩
    simpa only [p, ContinuousLinearEquiv.apply_symm_apply] using hC (q i) (s i) (hs i) a b
  apply (hlinear.comp hj (fun _ => M35.cylinderCoordinateEquiv.contDiff.contDiffAt) hA).congr
  intro i
  have hdom : ∀ᶠ y in 𝓝 (p i), (M35.cylinderCoordinateEquiv y).2 ∈
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (isOpen_Ioo.preimage (continuous_snd.comp M35.cylinderCoordinateEquiv.continuous)).mem_nhds
      (by simpa only [mem_preimage, Function.comp_apply, p,
        ContinuousLinearEquiv.apply_symm_apply] using hs i)
  filter_upwards [hmetric i, hdom] with y hy hdy
  exact (N.full_euclidean_coefficient (q i) hdy a b).symm.trans
    (congrArg (fun C : V →L[ℝ] V →L[ℝ] ℝ =>
      C (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) hy.symm)

end PoincareConjecture.EpsilonNeck
