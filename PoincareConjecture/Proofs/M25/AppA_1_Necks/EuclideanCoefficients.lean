import PoincareConjecture.Proofs.M25.AppA_1_Necks.EuclideanJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Parametrized.LinearEquiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

noncomputable def roundCylinderEuclideanModelCoefficients
    (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  RiemannianMetric.parameterBilinearEquiv (RiemannianMetric.lineModelEquiv 2).symm
    (roundCylinderModelCoefficients ((RiemannianMetric.lineModelEquiv 2).symm x))

theorem contDiff_roundCylinderEuclideanModelCoefficients :
    ContDiff ℝ ∞ roundCylinderEuclideanModelCoefficients := by
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  let P : (RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ) →L[ℝ]
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :=
    (RiemannianMetric.parameterBilinearEquiv T).toContinuousLinearMap
  have hP : ContDiff ℝ ∞ (P :
      (RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ) →
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ)
      (F := EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) P
  exact hP.comp (contDiff_roundCylinderModelCoefficients.comp T.contDiff)

theorem roundCylinderEuclideanModelCoefficients_basis
    (q : UnitTwoSphere) (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) (i j : Fin 3) :
    roundCylinderEuclideanModelCoefficients x
        (m25_roundCylinderEuclideanBasis i) (m25_roundCylinderEuclideanBasis j) =
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x) i j := by
  simp only [roundCylinderEuclideanModelCoefficients,
    RiemannianMetric.parameterBilinearEquiv_apply,
    m25_lineModelEquiv_symm_roundCylinderEuclideanBasis,
    roundCylinderModelCoefficients_apply, roundCylinderGram_eq_stereographic_formula,
    sub_zero, mul_one, Prod.fst_add, zero_add]

namespace EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

noncomputable def m25_normalizedEuclideanCoefficients (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  RiemannianMetric.parameterBilinearEquiv (RiemannianMetric.lineModelEquiv 2).symm
    (N.normalizedCenteredCoefficients q
      ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x))

theorem m25_normalizedEuclideanCoefficients_contDiffAt (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x).2 ∈
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContDiffAt ℝ ∞ (N.m25_normalizedEuclideanCoefficients q s) x := by
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  have hN : ContDiffAt ℝ ∞ (N.normalizedCenteredCoefficients q)
      ((0, s) + T x) := N.normalizedCenteredCoefficients_contDiffAt q hx
  have hphi : ContDiffAt ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin 3) => (0, s) + T y) x :=
    contDiffAt_const.add T.contDiff.contDiffAt
  let P : (RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ) →L[ℝ]
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) :=
    (RiemannianMetric.parameterBilinearEquiv T).toContinuousLinearMap
  have hP : ContDiff ℝ ∞ (P :
      (RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ) →
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ)
      (F := EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) P
  exact hP.contDiffAt.comp x
    (hN.comp (f := fun y : EuclideanSpace ℝ (Fin 3) => (0, s) + T y) x hphi)

theorem m25_normalizedEuclideanCoefficients_basis_eventuallyEq (N : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (i j : Fin 3) :
    (fun x => N.m25_normalizedEuclideanCoefficients q s x
      (m25_roundCylinderEuclideanBasis i) (m25_roundCylinderEuclideanBasis j)) =ᶠ[𝓝 0]
    (fun x : EuclideanSpace ℝ (Fin 3) => roundCylinderTensorCoefficient
      N.normalized_pullback (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x) i j) := by
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => (0, s) + T x) :=
    continuous_const.add T.continuous
  have hphi : Tendsto (fun x => (0, s) + T x) (𝓝 0) (𝓝 (0, s)) := by
    simpa only [map_zero, add_zero] using hc.tendsto 0
  have h := (N.normalizedCenteredCoefficients_basis_eventuallyEq q
    (y := (0, s)) hs i j).comp_tendsto hphi
  simpa only [Function.comp_def, m25_normalizedEuclideanCoefficients,
    RiemannianMetric.parameterBilinearEquiv_apply,
    m25_lineModelEquiv_symm_roundCylinderEuclideanBasis, T] using h.symm

theorem m25_exists_normalizedEuclideanCoefficients_scalar_twoJet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ},
      s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → ∀ r : ℕ, r ≤ 2 → ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ r (fun x => N.m25_normalizedEuclideanCoefficients q s x
          (m25_roundCylinderEuclideanBasis i) (m25_roundCylinderEuclideanBasis j)) 0 -
        iteratedFDeriv ℝ r (fun x => roundCylinderEuclideanModelCoefficients x
          (m25_roundCylinderEuclideanBasis i) (m25_roundCylinderEuclideanBasis j)) 0‖ ≤
        C * N.epsilon := by
  obtain ⟨C, hC, hbound⟩ := exists_normalized_pullback_euclidean_scalar_twoJet_bound.{u}
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ g N q s hs r hr i j
  have hA := ((N.m25_normalizedEuclideanCoefficients_contDiffAt q s (x := 0)
    (by simpa only [map_zero, add_zero] using hs)).clm_apply
    (contDiffAt_const (c := m25_roundCylinderEuclideanBasis i))).clm_apply
      (contDiffAt_const (c := m25_roundCylinderEuclideanBasis j))
  have hB := ((contDiff_roundCylinderEuclideanModelCoefficients.contDiffAt
    (x := 0)).clm_apply
    (contDiffAt_const (c := m25_roundCylinderEuclideanBasis i))).clm_apply
      (contDiffAt_const (c := m25_roundCylinderEuclideanBasis j))
  have heq := (N.m25_normalizedEuclideanCoefficients_basis_eventuallyEq q hs i j).sub
    (Eventually.of_forall (fun x =>
      roundCylinderEuclideanModelCoefficients_basis q s x i j))
  rw [← iteratedFDeriv_sub_apply (hA.of_le (by exact_mod_cast le_top))
    (hB.of_le (by exact_mod_cast le_top)), (heq.iteratedFDeriv ℝ r).self_of_nhds]
  exact hbound N q hs r hr i j

end EpsilonNeck

end PoincareConjecture
