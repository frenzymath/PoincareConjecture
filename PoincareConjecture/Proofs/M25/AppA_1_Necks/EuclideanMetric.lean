import PoincareConjecture.Proofs.M25.AppA_1_Necks.AmbientScalar
import PoincareConjecture.Proofs.M25.AppA_1_Necks.ModelMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem RiemannianMetric.lineModelEquiv_norm_sq {n : ℕ}
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖v‖ ^ 2 = ‖((lineModelEquiv n).symm v).1‖ ^ 2 +
      ((lineModelEquiv n).symm v).2 ^ 2 := by
  change ‖v‖ ^ 2 = ‖Poincare.EuclideanSpace.euclideanTail v‖ ^ 2 + (v 0) ^ 2
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ,
    Poincare.EuclideanSpace.euclideanTail_apply]
  ring

theorem roundCylinderEuclideanModelCoefficients_zero
    (v : EuclideanSpace ℝ (Fin 3)) :
    roundCylinderEuclideanModelCoefficients 0 v v =
      2 * ‖((RiemannianMetric.lineModelEquiv 2).symm v).1‖ ^ 2 +
        ((RiemannianMetric.lineModelEquiv 2).symm v).2 ^ 2 := by
  simp only [roundCylinderEuclideanModelCoefficients,
    RiemannianMetric.parameterBilinearEquiv_apply, roundCylinderModelCoefficients_apply,
    map_zero, Prod.fst_zero, norm_zero, real_inner_self_eq_norm_sq]
  norm_num
  ring

theorem norm_sq_le_roundCylinderEuclideanModelCoefficients
    (v : EuclideanSpace ℝ (Fin 3)) :
    ‖v‖ ^ 2 ≤ roundCylinderEuclideanModelCoefficients 0 v v := by
  rw [RiemannianMetric.lineModelEquiv_norm_sq,
    roundCylinderEuclideanModelCoefficients_zero]
  nlinarith [sq_nonneg ‖((RiemannianMetric.lineModelEquiv 2).symm v).1‖]

namespace EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

private theorem centeredCoefficients_pullback (N : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v w : RoundCylinderCoordinates) :
    N.normalizedCenteredCoefficients q (0, s) v w =
      N.normalized_pullback (q, s)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 v.1, v.2)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 w.1, w.2) := by
  let T : RoundCylinderCoordinates →L[ℝ] RoundCylinderTangent (q, s) :=
    ((mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0).comp
      (ContinuousLinearMap.fst ℝ _ _)).prod (ContinuousLinearMap.snd ℝ _ _)
  let P := (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
    N.coordinate_map (q, s)).comp T
  let : NormedAddCommGroup (TangentSpace (𝓡 3) (N.coordinate_map (q, s))) := by
    unfold TangentSpace
    infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 3) (N.coordinate_map (q, s))) := by
    unfold TangentSpace
    infer_instance
  let B := N.scale⁻¹ ^ 2 • (g.inner (N.coordinate_map (q, s))).bilinearComp P P
  have hb (i j : Fin 3) :
      N.normalizedCenteredCoefficients q (0, s)
          (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) =
        B (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) := by
    have h := (N.normalizedCenteredCoefficients_basis_eventuallyEq q
      (y := (0, s)) hs i j).self_of_nhds.symm
    dsimp only [roundCylinderTensorCoefficient] at h
    erw [sphere_chart_symm_zero] at h
    exact h
  change N.normalizedCenteredCoefficients q (0, s) v w = B v w
  rw [cylinderCoordinate_decomposition v, cylinderCoordinate_decomposition w]
  simp only [map_add, map_smul, add_apply, smul_apply, hb]

theorem euclideanParametrization_mfderiv_axial (N : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) 0
        (m25_roundCylinderEuclideanBasis 2) =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (q, s) (0, 1) := by
  let L := ContinuousLinearMap.toSpanSingleton ℝ (m25_roundCylinderEuclideanBasis 2)
  let c : ℝ → RoundCylinderSpace := fun t => (q, s + t)
  have hline : HasFDerivAt (fun t : ℝ => s + t) (ContinuousLinearMap.id ℝ ℝ) 0 :=
    (hasFDerivAt_id 0).const_add s
  have hc : ContMDiff 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ c :=
    contMDiff_const.prodMk (contMDiff_const.add contMDiff_id)
  have hcder : mfderiv 𝓘(ℝ, ℝ) ((𝓡 2).prod 𝓘(ℝ, ℝ)) c 0 1 = (0, 1) := by
    rw [mfderiv_prodMk mdifferentiableAt_const hline.differentiableAt.mdifferentiableAt,
      mfderiv_const, mfderiv_eq_fderiv, hline.fderiv]
    rfl
  have hcomp : N.euclideanParametrization q s ∘ L = N.coordinate_map ∘ c := by
    funext t
    simp [euclideanParametrization, centeredParametrization, L, c,
      m25_lineModelEquiv_symm_roundCylinderEuclideanBasis, roundCylinderCoordinateBasis,
      sphere_chart_symm_zero]
  have hE := (N.euclideanParametrization_contMDiffAt q s (x := 0)
    (by simpa only [map_zero, add_zero] using hs)).mdifferentiableAt (by simp)
  have hN := (N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show (q, s) ∈ (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) from
        ⟨mem_univ q, hs⟩))).mdifferentiableAt (by simp)
  have hleft := mfderiv_comp_apply 0
    (show MDifferentiableAt (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) (L 0) by
      simpa only [map_zero] using hE) L.mdifferentiableAt (1 : ℝ)
  have hright := mfderiv_comp_apply 0
    (show MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map (c 0) by
      simpa only [c, add_zero] using hN) (hc.mdifferentiableAt (by simp)) (1 : ℝ)
  rw [hcomp] at hleft
  rw [hcder] at hright
  have h := hleft.symm.trans hright
  let dE : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) := fun x v =>
    mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) x v
  let dN : RoundCylinderSpace → RoundCylinderCoordinates → EuclideanSpace ℝ (Fin 3) :=
    fun z v => mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v
  change dE (L 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) L 0 1) = dN (c 0) (0, 1) at h
  rw [L.mfderiv_eq] at h
  change dE (L 0) ((1 : ℝ) • m25_roundCylinderEuclideanBasis 2) = dN (c 0) (0, 1) at h
  change dE 0 (m25_roundCylinderEuclideanBasis 2) = dN (q, s) (0, 1)
  simpa only [map_zero, one_smul, c, add_zero] using h

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem normalizedEuclideanCoefficients_quadratic_error (N : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : EuclideanSpace ℝ (Fin 3)) :
    |N.m25_normalizedEuclideanCoefficients q s 0 v v -
        roundCylinderEuclideanModelCoefficients 0 v v| ≤
      N.epsilon * roundCylinderEuclideanModelCoefficients 0 v v := by
  let w := (RiemannianMetric.lineModelEquiv 2).symm v
  let u : RoundCylinderTangent (q, s) :=
    (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 w.1, w.2)
  have hmodel : EvolvingRoundCylinderMetric 0 (q, s) u u =
      roundCylinderEuclideanModelCoefficients 0 v v := by
    have hinner := roundSphereMetric_chart_symm_inner q 0 w.1 w.1
    rw [sphere_chart_symm_zero] at hinner
    change 2 * (1 - 0) * (roundSphereMetric 2).inner q
      (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 w.1)
      (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 w.1) +
        w.2 * w.2 = _
    erw [hinner]
    simp only [roundCylinderEuclideanModelCoefficients,
      RiemannianMetric.parameterBilinearEquiv_apply, roundCylinderModelCoefficients_apply,
      map_zero, Prod.fst_zero, norm_zero, sub_zero, mul_one]
    norm_num
    rfl
  have h := N.normalized_pullback_quadratic_error (z := (q, s)) hs u
  rw [hmodel] at h
  simpa only [m25_normalizedEuclideanCoefficients,
    RiemannianMetric.parameterBilinearEquiv_apply, map_zero, add_zero,
    centeredCoefficients_pullback N q hs, w, u] using h

theorem euclideanParametrization_mfderiv_bijective (N : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) 0) := by
  obtain ⟨h, _, V, _, h0, hstrip, heq⟩ :=
    N.m25_exists_normalizedEuclideanCoefficients_realization q hs
  have hc : 0 < N.scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  apply h.mfderiv_bijective_of_pullback_eq (rescaledMetric g (N.scale⁻¹ ^ 2) hc) 0
  intro v w
  change _ = h.euclideanCoefficients 0 v w
  rw [heq 0 h0, rescaledMetric_inner]
  exact (N.normalizedEuclideanCoefficients_pullback q s (hstrip 0 h0) v w).symm

noncomputable def normalizedEuclideanFrame (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] TangentSpace (𝓡 3) (N.coordinate_map (q, s)) :=
  N.scale⁻¹ • mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) 0

theorem normalizedEuclideanFrame_bijective (N : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    Function.Bijective (N.normalizedEuclideanFrame q s) := by
  let F : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) 0
  have hF : Function.Bijective F := N.euclideanParametrization_mfderiv_bijective q hs
  change Function.Bijective (fun v : EuclideanSpace ℝ (Fin 3) => N.scale⁻¹ • F v)
  constructor
  · intro v w hvw
    apply hF.1
    have h := congrArg (fun z => N.scale • z) hvw
    simpa only [smul_smul, mul_inv_cancel₀ N.scale_pos.ne', one_smul] using h
  · intro w
    obtain ⟨v, hv⟩ := hF.2 (N.scale • w)
    refine ⟨v, ?_⟩
    simp only [hv, smul_smul, inv_mul_cancel₀ N.scale_pos.ne', one_smul]

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem normalizedEuclideanFrame_inner (N : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v w : EuclideanSpace ℝ (Fin 3)) :
    g.inner (N.coordinate_map (q, s))
        (N.normalizedEuclideanFrame q s v) (N.normalizedEuclideanFrame q s w) =
      N.m25_normalizedEuclideanCoefficients q s 0 v w := by
  let F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 3) (𝓡 3) (N.euclideanParametrization q s) 0
  have h := N.normalizedEuclideanCoefficients_pullback q s
    (x := 0) (by simpa only [map_zero, add_zero] using hs) v w
  change N.m25_normalizedEuclideanCoefficients q s 0 v w =
    N.scale⁻¹ ^ 2 * g.inner (N.euclideanParametrization q s 0) (F v) (F w) at h
  rw [N.euclideanParametrization_zero] at h
  change g.inner (N.coordinate_map (q, s)) (N.scale⁻¹ • F v) (N.scale⁻¹ • F w) = _
  simpa only [map_smul, smul_apply, smul_eq_mul, pow_two, mul_assoc] using h.symm

end EpsilonNeck

end PoincareConjecture
