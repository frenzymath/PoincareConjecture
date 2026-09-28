import PoincareConjecture.Proofs.M25.AppA_1_Necks.EuclideanCoefficients
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets.Ellipticity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem m25_normalizedEuclideanCoefficients_symm (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) (x v w : EuclideanSpace ℝ (Fin 3)) :
    N.m25_normalizedEuclideanCoefficients q s x v w =
      N.m25_normalizedEuclideanCoefficients q s x w v := by
  simp only [m25_normalizedEuclideanCoefficients,
    RiemannianMetric.parameterBilinearEquiv_apply, normalizedCenteredCoefficients,
    smul_apply, smul_eq_mul, RiemannianMetric.parametrizedCoefficients_apply]
  rw [g.symm]

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem m25_exists_normalizedEuclideanCoefficients_realization (N : EpsilonNeck g)
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ∃ (h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)))
      (_D : LeviCivitaData h) (V : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen V ∧ 0 ∈ V ∧
        (∀ x ∈ V, ((0, s) + (RiemannianMetric.lineModelEquiv 2).symm x).2 ∈
          Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) ∧
        ∀ x ∈ V, h.euclideanCoefficients x = N.m25_normalizedEuclideanCoefficients q s x := by
  let T := (RiemannianMetric.lineModelEquiv 2).symm
  let B := N.normalizedCenteredCoefficients q
  let phi := fun x : EuclideanSpace ℝ (Fin 3) => (0, s) + T x
  let eta := (1 - N.epsilon) / 2
  have heta : 0 < eta := by dsimp [eta]; linarith [N.epsilon_lt_half]
  have hphi : Continuous phi := continuous_const.add T.continuous
  have hphi0 : Tendsto phi (𝓝 0) (𝓝 (0, s)) := by
    simpa only [phi, map_zero, add_zero] using hphi.tendsto 0
  have hBcenter : Tendsto B (𝓝 (0, s)) (𝓝 (B (0, s))) :=
    (N.normalizedCenteredCoefficients_contDiffAt q (y := (0, s)) hs).continuousAt
  have hB : Tendsto (fun x => B (phi x)) (𝓝 0) (𝓝 (B (0, s))) :=
    Filter.Tendsto.comp (f := phi) (g := B) hBcenter hphi0
  have hsmall : {x | ‖B (phi x) - B (0, s)‖ < eta} ∈ 𝓝 0 := by
    have h := hB (Metric.ball_mem_nhds _ heta)
    change {x | dist (B (phi x)) (B (0, s)) < eta} ∈ 𝓝 0 at h
    simpa only [dist_eq_norm] using h
  have hstrip : {x | (phi x).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹} ∈ 𝓝 0 :=
    (continuous_snd.tendsto (0, s)).comp hphi0 (isOpen_Ioo.mem_nhds hs)
  obtain ⟨U, hU, hUopen, h0U⟩ := mem_nhds_iff.mp (inter_mem hstrip hsmall)
  have hpos (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ U)
      (v : EuclideanSpace ℝ (Fin 3)) (hv : v ≠ 0) :
      0 < N.m25_normalizedEuclideanCoefficients q s x v v := by
    have hw : T v ≠ 0 := by
      intro h
      apply hv
      exact T.injective (h.trans T.map_zero.symm)
    have hn : 0 < ‖T v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
    have hlower := N.normalizedCenteredCoefficients_lower q hs (T v)
    have herror := (B (phi x) - B (0, s)).le_opNorm₂ (T v) (T v)
    have hnorm := (hU hx).2
    have herror' : |B (phi x) (T v) (T v) - B (0, s) (T v) (T v)| <
        eta * ‖T v‖ ^ 2 := by
      calc
        _ ≤ ‖B (phi x) - B (0, s)‖ * ‖T v‖ ^ 2 := by
          simpa only [sub_apply, Real.norm_eq_abs,
            pow_two, mul_assoc] using herror
        _ < eta * ‖T v‖ ^ 2 := mul_lt_mul_of_pos_right hnorm hn
    have hl := (abs_lt.mp herror').1
    change 0 < B (phi x) (T v) (T v)
    change (1 - N.epsilon) * ‖T v‖ ^ 2 ≤ B (0, s) (T v) (T v) at hlower
    have hmargin : 0 < (1 - N.epsilon) / 2 * ‖T v‖ ^ 2 := mul_pos heta hn
    dsimp [eta] at hl
    nlinarith [hmargin]
  obtain ⟨h, D, V, hVopen, h0V, hVU, hVeq⟩ :=
    RiemannianMetric.exists_local_realization hUopen h0U
      (N.m25_normalizedEuclideanCoefficients q s)
      (fun x hx => (N.m25_normalizedEuclideanCoefficients_contDiffAt q s
        (show (phi x).2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ from (hU hx).1)).contDiffWithinAt)
      (fun x _ v w => N.m25_normalizedEuclideanCoefficients_symm q s x v w) hpos
  exact ⟨h, D, V, hVopen, h0V, fun x hx => (hU (hVU hx)).1, hVeq⟩

theorem exists_normalizedEuclideanMetric_scalar_twoJet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ},
      s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)),
      h.euclideanCoefficients =ᶠ[𝓝 0] N.m25_normalizedEuclideanCoefficients q s →
      ∀ r : ℕ, r ≤ 2 → ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ r (fun x => h.inner x
          (m25_roundCylinderEuclideanBasis i) (m25_roundCylinderEuclideanBasis j)) 0 -
        iteratedFDeriv ℝ r (fun x => roundCylinderEuclideanModelCoefficients x
          (m25_roundCylinderEuclideanBasis i) (m25_roundCylinderEuclideanBasis j)) 0‖ ≤
        C * N.epsilon := by
  obtain ⟨C, hC, hbound⟩ := m25_exists_normalizedEuclideanCoefficients_scalar_twoJet_bound.{u}
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ g N q s hs h heq r hr i j
  have hscalar : (fun x => h.inner x
      (m25_roundCylinderEuclideanBasis i) (m25_roundCylinderEuclideanBasis j)) =ᶠ[𝓝 0]
      (fun x => N.m25_normalizedEuclideanCoefficients q s x
        (m25_roundCylinderEuclideanBasis i) (m25_roundCylinderEuclideanBasis j)) := by
    filter_upwards [heq] with x hx
    exact congrArg (fun A => A (m25_roundCylinderEuclideanBasis i)
      (m25_roundCylinderEuclideanBasis j)) hx
  rw [(hscalar.iteratedFDeriv ℝ r).self_of_nhds]
  exact hbound N q hs r hr i j

end PoincareConjecture.EpsilonNeck
