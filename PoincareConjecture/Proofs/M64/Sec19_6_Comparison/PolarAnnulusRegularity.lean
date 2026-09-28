import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.PolarAnnulusMap
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.LipschitzArea
import PoincareConjecture.Proofs.M60.Mathlib.NullSphere

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Metric
open scoped Manifold ContDiff Bundle NNReal ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem m64Annulus_polar_traces (A : M64Annulus g c0 c1) (theta : ℝ) :
    m64PolarAnnulusMap A.map ((1 / 2 : ℝ) • Proofs.M58.angularPoint theta) = c0 theta ∧
      m64PolarAnnulusMap A.map (Proofs.M58.angularPoint theta) = c1 theta := by
  constructor
  · have h := m64PolarAnnulusMap_polar A.periodic (r := 1 / 2) (by norm_num) theta
    norm_num at h
    exact h.trans (A.lower_boundary theta)
  · have h := m64PolarAnnulusMap_polar A.periodic (r := 1) zero_lt_one theta
    norm_num at h
    exact h.trans (A.upper_boundary theta)

theorem m64Annulus_polar_lipschitz [T2Space M] (A : M64Annulus g c0 c1) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ x ∈ loopDiskSet ∩ {z : LoopPlane | 1 / 2 ≤ ‖z‖},
        ∀ y ∈ loopDiskSet ∩ {z : LoopPlane | 1 / 2 ≤ ‖z‖},
          g.edist (m64PolarAnnulusMap A.map x) (m64PolarAnnulusMap A.map y) ≤
            ENNReal.ofReal L * ENNReal.ofReal ‖x - y‖ := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hLip : LipschitzOnWith (NNReal.mk A.lipschitz_constant A.lipschitz_nonnegative)
      A.map m64AnnulusDomain := by
    intro x hx y hy
    change g.edist (A.map x) (A.map y) ≤ _
    simpa only [edist_dist, dist_eq_norm,
      ENNReal.ofReal_eq_coe_nnreal A.lipschitz_nonnegative] using
      A.lipschitz_on_domain ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨L, hL⟩ := m64PolarAnnulusMap_lipschitz A.periodic hLip
  refine ⟨L, L.property, ?_⟩
  intro x hx y hy
  have hxQ : 1 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 :=
    ⟨hx.2, mem_closedBall_zero_iff.mp hx.1⟩
  have hyQ : 1 / 2 ≤ ‖y‖ ∧ ‖y‖ ≤ 1 :=
    ⟨hy.2, mem_closedBall_zero_iff.mp hy.1⟩
  have h := hL hxQ hyQ
  change g.edist (m64PolarAnnulusMap A.map x) (m64PolarAnnulusMap A.map y) ≤
    (L : ℝ≥0∞) * edist x y at h
  simpa only [edist_dist, dist_eq_norm, ENNReal.ofReal_coe_nnreal] using h

theorem m64Annulus_polar_area_integrable [T2Space M] (A : M64Annulus g c0 c1) :
    IntegrableOn (m60AreaDensity g (m64PolarAnnulusMap A.map))
      ((closedBall (0 : LoopPlane) (1 / 2))ᶜ ∩ loopDiskSet) volume := by
  let Q : Set LoopPlane := (closedBall (0 : LoopPlane) (1 / 2))ᶜ ∩ ball (0 : LoopPlane) 1
  have hQ : IsOpen Q := isClosed_closedBall.isOpen_compl.inter isOpen_ball
  have hsub : Q ⊆ loopDiskSet ∩ {z : LoopPlane | 1 / 2 ≤ ‖z‖} := by
    intro z hz
    have hz0 : 1 / 2 < ‖z‖ := by
      simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hz.1
    exact ⟨ball_subset_closedBall hz.2, hz0.le⟩
  have hfinite : volume Q ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_closedBall (0 : LoopPlane) 1).measure_lt_top.ne
      (measure_mono (fun _ hz => (hsub hz).1))
  obtain ⟨L, hL, hLip⟩ := m64Annulus_polar_lipschitz A
  obtain ⟨hi, _⟩ := m60AreaIntegral_bound_of_metric_lipschitzOn g hQ hfinite hL
    (fun x hx y hy => hLip x (hsub hx) y (hsub hy))
  have heq : Q =ᵐ[volume]
      ((closedBall (0 : LoopPlane) (1 / 2))ᶜ ∩ loopDiskSet : Set LoopPlane) := by
    filter_upwards [M60.haar_ball_ae_eq_closedBall volume (0 : LoopPlane) 1] with z hz
    exact congrArg (fun b : Prop => z ∈ (closedBall (0 : LoopPlane) (1 / 2))ᶜ ∧ b) hz
  exact (integrableOn_congr_set_ae heq).mp hi

end PoincareConjecture
