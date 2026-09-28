import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialPastSlab
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialSlabCoefficients
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialPastError

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M47

open M36 M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_source_initial_past_comparison (P : M47Predecessors.{u})
    {zeta K : ℝ} (hzeta : 0 < zeta) (hzetaSmall : zeta ≤ 1 / 8)
    (hK : 0 < K) (m : ℕ) :
    ∃ Cerror Lerror : ℝ, 0 < Cerror ∧ 0 ≤ Lerror ∧
      ∀ {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
      {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
      {T q left R : ℝ}, R + 1 < N.epsilon⁻¹ →
      m ≤ ⌊N.epsilon⁻¹⌋₊ → left ≤ -1 - 4 * zeta →
      ∀ (U : TopologicalSpace.Opens C.carrier),
      (U : Set C.carrier) = N.region (-(R + 1)) (R + 1) →
      (U : Set C.carrier).Nonempty →
      ∀ (D : SurgeryFlowCylinder F C T q (Icc left (-1 / 2)) U)
        (old : SurgeryFlowCylinder F C T q (Ioo (-1 : ℝ) 0) N.carrier),
      (∀ v (hv : v ∈ Icc left (-1 / 2)) (hraw : v ∈ Ioo (-1 : ℝ) 0),
        ∀ x ∈ U, D.forward v hv x = old.forward v hraw x) →
      (∀ v ∈ Ioo (-1 : ℝ) 0,
        RoundCylinderClose N.epsilon v (surgeryCylinderPullback old N.coordinate_map v)) →
      (∀ v (hv : v ∈ Icc left (-1 / 2)),
        v ∈ Icc (-1 - 4 * zeta) (-1 + zeta) → ∀ x ∈ U,
          (F.connection (T + v / q)).curvatureTensorNorm (D.forward v hv x) ≤ K * q) →
      let raw := fun s : ℝ => -1 + zeta + s
      ∃ hmem : MapsTo raw (Icc (-(5 * zeta)) 0) (Icc left (-1 / 2)),
        ∃ G : RicciFlow 3 U (Icc (-(5 * zeta)) 0),
          (∀ s (hs : s ∈ Icc (-(5 * zeta)) 0) (x : U),
            (∀ v w : TangentSpace (𝓡 3) x,
              (G.metric s).inner x v w = D.pullbackInner (raw s) (hmem hs) x.val
                (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
                (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)) ∧
            (G.connection s).scalarCurvature x =
              (F.connection (T + raw s / q)).scalarCurvature
                (D.forward (raw s) (hmem hs) x.val) / q ∧
            (G.connection s).curvatureTensorNorm x =
              (F.connection (T + raw s / q)).curvatureTensorNorm
                (D.forward (raw s) (hmem hs) x.val) / q) ∧
          (∀ s ∈ Icc (-(5 * zeta)) 0, ∀ x : U,
            (G.connection s).curvatureTensorNorm x ≤ K) ∧
          ∀ (theta : UnitTwoSphere) (c : ℝ), |c| ≤ R →
            ∃ Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E U ∞,
              Phi.source = Metric.ball 0 (1 / 2) ∧
              (∀ p ∈ Metric.ball (0 : E) (1 / 2),
                (Phi p).val = centeredNeckLift N theta c p) ∧
              (∀ s ∈ Ioc (-zeta) 0, ∀ p ∈ Metric.ball (0 : E) (1 / 2),
                (G.metric s).pullbackCoefficients Phi p =
                  centeredCylinderMetric (surgeryCylinderPullback old N.coordinate_map (raw s))
                    theta c p) ∧
              ∀ {omega : ℝ}, 0 ≤ omega → omega ≤ zeta / 2 →
              ∀ s ∈ Icc (-zeta - omega) (-zeta), ∀ j ≤ m,
                ‖iteratedFDeriv ℝ j ((G.metric s).pullbackCoefficients Phi) (0 : E) -
                  iteratedFDeriv ℝ j (evolvingCylinderModelField (raw s)) (0 : E)‖ ≤
                    Cerror * N.epsilon + Lerror * omega := by
  classical
  choose Cj Lj hCj hLj herror using fun j => source_initial_chart_past_error P.m04
    (R := 1 / 2) (rho := 1 / 8) (a := 1 / 2) (b := 6)
      hzeta hzetaSmall hK (by norm_num) (by norm_num) (by norm_num) (by norm_num) j
  let Cerror := 1 + ∑ j ∈ Finset.range (m + 1), Cj j
  let Lerror := ∑ j ∈ Finset.range (m + 1), Lj j
  have hCsum : 0 ≤ ∑ j ∈ Finset.range (m + 1), Cj j :=
    Finset.sum_nonneg fun j _ => (hCj j).le
  have hLsum : 0 ≤ Lerror := Finset.sum_nonneg fun j _ => hLj j
  have hCbound (j : ℕ) (hj : j ≤ m) : Cj j ≤ Cerror := by
    have h := Finset.single_le_sum (fun k _ => (hCj k).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    dsimp only [Cerror]
    linarith only [h]
  have hLbound (j : ℕ) (hj : j ≤ m) : Lj j ≤ Lerror :=
    Finset.single_le_sum (fun k _ => hLj k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  refine ⟨Cerror, Lerror, by dsimp only [Cerror]; linarith only [hCsum], hLsum, ?_⟩
  intro F C g N T q left R hbuffer horder hleft U hU hne D old hagreement hclose hcurv
  let raw := fun s : ℝ => -1 + zeta + s
  obtain ⟨hmem, G, hread, hGcurv⟩ := exists_source_initial_past_slab P hzeta hzetaSmall
    hleft U hne D hcurv
  refine ⟨hmem, G, hread, hGcurv, ?_⟩
  intro theta c hc
  obtain ⟨Phi, hsource, hmap, _hzero⟩ :=
    exists_source_initial_neck_chart N hc hbuffer U hU theta
  have hdomain : Metric.ball (0 : E) (1 / 2) ⊆ centeredNeckDomain N c := by
    intro p hp
    have hp' : ‖p‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hp
    have hheight : |cylinderHeightCovector p| ≤ ‖p‖ := by
      change |p 2| ≤ ‖p‖
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p (2 : Fin 3)
    have hsum : |cylinderHeightCovector p + c| < N.epsilon⁻¹ :=
      (abs_add_le _ _).trans_lt (by linarith only [hheight, hp', hc, hbuffer])
    exact abs_lt.mp hsum
  have htime (s : ℝ) (hs : s ∈ Ioc (-zeta) 0) : raw s ∈ Ioo (-1 : ℝ) 0 := by
    dsimp only [raw]
    constructor <;> linarith only [hs.1, hs.2, hzetaSmall]
  have hslab (s : ℝ) (hs : s ∈ Ioc (-zeta) 0) : s ∈ Icc (-(5 * zeta)) 0 :=
    ⟨by linarith only [hs.1, hzeta], hs.2⟩
  have hcoeff (s : ℝ) (hs : s ∈ Ioc (-zeta) 0) (p : E)
      (hp : p ∈ Metric.ball 0 (1 / 2)) :
      (G.metric s).pullbackCoefficients Phi p =
        centeredCylinderMetric
          (surgeryCylinderPullback old N.coordinate_map (raw s)) theta c p := by
    exact source_initial_slab_coefficients N U D old (raw s) (hmem (hslab s hs))
      (htime s hs) (hagreement _ _ _) (G.metric s) (fun x => (hread s (hslab s hs) x).1)
      theta c Phi hsource hmap hdomain hp
  have hzero : (0 : ℝ) ∈ Ioc (-zeta) 0 := ⟨by linarith only [hzeta], le_rfl⟩
  have hterminal : ∀ p ∈ Metric.closedBall (0 : E) (2 * (1 / 8 : ℝ)), ∀ v,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ (G.metric 0).pullbackCoefficients Phi p v v ∧
        (G.metric 0).pullbackCoefficients Phi p v v ≤ 6 * ‖v‖ ^ 2 := by
    intro p hp v
    have hpOpen : p ∈ Metric.ball (0 : E) (1 / 2) :=
      Metric.closedBall_subset_ball (by norm_num) hp
    rw [hcoeff 0 hzero p hpOpen]
    obtain ⟨L, hL⟩ := source_initial_cylinder_tensor_bilinear old N.coordinate_map
      (raw 0) (htime 0 hzero) (centeredCylinderLift theta c p)
    have hpNorm : ‖p‖ ≤ 2 * (1 / 8 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hp
    exact source_initial_centered_metric_bounds N.epsilon_pos N.epsilon_lt_half.le
      ⟨(htime 0 hzero).1.le, (htime 0 hzero).2.le⟩ (hclose _ (htime 0 hzero)) theta c p
      (hdomain hpOpen) ((cap_box_horizontal_norm_le p).trans (by linarith only [hpNorm])) L hL v
  have hnative : c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    apply abs_lt.mp
    linarith only [hc, hbuffer]
  refine ⟨Phi, hsource, hmap, hcoeff, ?_⟩
  intro omega homega homegaSmall s hs j hj
  have hbound := herror j G Phi hsource (fun t ht x _ => hGcurv t ht x) hterminal
    N.epsilon_pos N.epsilon_lt_half.le (hj.trans horder)
    (fun t => surgeryCylinderPullback old N.coordinate_map (raw t)) (theta, c) hnative
    (fun t ht => hclose _ (htime t ht))
    (fun t ht => by
      filter_upwards [Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))] with p hp
      exact hcoeff t ht p hp) homega homegaSmall s hs
  exact hbound.trans (add_le_add
    (mul_le_mul_of_nonneg_right (hCbound j hj) N.epsilon_pos.le)
    (mul_le_mul_of_nonneg_right (hLbound j hj) homega))

end PoincareConjecture.M47
