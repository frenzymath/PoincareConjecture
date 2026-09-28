import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialNearEdgeGrowth
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakMinimizerPowerGrowth
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyLocalRepresentative
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakRepresentative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [T2Space M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "O" => m64AnnulusLowerDomain
local notation "S" => interior m64AnnulusDomain
local notation "L" => m64AnnulusLowerStrip

theorem lower_local_column_power_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc0P : Function.Periodic c0 curvePeriod)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hpos : ∀ q v, 0 ≤ Q q v v) {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.energy Q ≤ B.energy Q)
    (a : LoopPlane) (ha : a ∈ O) :
    ∃ rho : ℝ, 0 < rho ∧ closedBall a (2 * rho) ⊆ O ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∃ beta : ℝ, 0 < beta ∧
        ∀ b ∈ closedBall a rho, ∀ r ∈ Ioc (0 : ℝ) rho, ∀ i : Fin 2,
          (∫ p in ball b r, ‖A.lowerExtensionColumn i p‖ ^ 2) ≤ K * r ^ beta := by
  rcases lt_trichotomy (a 1) 0 with hneg | hzero | hposA
  · have haL : a ∈ L :=
      (m64AnnulusLowerStrip_coordinates a).mpr ⟨ha.1, ha.2.1, ha.2.2.1, hneg⟩
    obtain ⟨delta, hdelta, hdeltaL⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (m64AnnulusLowerStrip_isOpen.mem_nhds haL)
    let rho := delta / 4
    have hrho : 0 < rho := by dsimp [rho]; positivity
    have hlarge : closedBall a (2 * rho) ⊆ L :=
      (closedBall_subset_closedBall (show 2 * rho ≤ delta from by dsimp [rho]; linarith)).trans
        hdeltaL
    obtain ⟨D, hD, hgrowth⟩ := A.lower_smooth_column_power_growth he hc0 hc0P
    refine ⟨rho, hrho, hlarge.trans m64AnnulusLower_strip_subset,
      Real.pi * D ^ 2, by positivity, 2, by norm_num, ?_⟩
    intro b hb r hr i
    have hbound := hgrowth a ha hneg rho hrho hlarge b hb r hr i
    refine hbound.trans_eq ?_
    rw [EuclideanSpace.volume_ball_fin_two]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, Real.rpow_two,
      ENNReal.toReal_ofReal hr.1.le, ENNReal.toReal_ofReal Real.pi_pos.le]
    ring
  · exact A.lower_near_edge_column_power_growth g he hei hread hc0 hc0P
      Q hQ hpos hC hcoercive hmin ha hzero
  · have haS : a ∈ S :=
      (m64AnnulusInterior_coordinates a).mpr ⟨ha.1, ha.2.1, hposA, ha.2.2.2⟩
    obtain ⟨rho, hrho, hlarge, K, hK, beta, hbeta, hgrowth⟩ :=
      A.local_column_power_growth g he hei hread Q hQ hpos hC hcoercive hmin a haS
    refine ⟨rho, hrho, hlarge.trans m64AnnulusLower_rect_subset, K, hK, beta, hbeta, ?_⟩
    intro b hb r hr i
    have hball : ball b r ⊆ S := ball_subset_closedBall.trans
      ((closedBall_subset_closedBall' (show r + dist b a ≤ 2 * rho from by
        linarith [mem_closedBall.mp hb, hr.2])).trans hlarge)
    calc
      _ = ∫ p in ball b r, ‖A.column i p‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
        rw [lowerExtensionColumn, m64AnnulusLowerExtend_right _ _ (hball hp)]
      _ ≤ K * r ^ beta := hgrowth b hb r hr i

private theorem lower_edge_mem_closure {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) curvePeriod) :
    annulusPoint x 0 ∈ closure L := by
  apply Metric.mem_closure_iff.mpr
  intro epsilon hepsilon
  let d := min epsilon 1 / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d < 1 := by dsimp [d]; linarith [min_le_right epsilon 1]
  have hde : d < epsilon := by dsimp [d]; linarith [min_le_left epsilon 1]
  refine ⟨annulusPoint x (-d), ?_, ?_⟩
  · exact (m64AnnulusLowerStrip_coordinates _).mpr
      ⟨hx.1, hx.2, by change -1 < -d; linarith, by change -d < 0; linarith⟩
  · rw [dist_comm]
    change dist (annulusPoint x (-d)) (annulusPoint ((annulusPoint x (-d)) 0) 0) < epsilon
    rw [m64RadialAxis_dist]
    simpa only [show (annulusPoint x (-d)) 1 = -d from rfl, abs_neg, abs_of_pos hd] using hde

theorem lower_continuous_representative
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc0P : Function.Periodic c0 curvePeriod)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hpos : ∀ q v, 0 ≤ Q q v v) {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.energy Q ≤ B.energy Q) :
    ∃ F : LoopPlane → M, ContinuousOn F O ∧
      F =ᵐ[volume.restrict O] A.lowerExtensionMap ∧
      ∀ x ∈ Ioo (0 : ℝ) curvePeriod, F (annulusPoint x 0) = c0 x := by
  have hce : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he.comp hc0)
  have hdata := A.lower_extension_memLp hce
  obtain ⟨U, hU, hUae⟩ := m64Morrey_local_representative hdata.1 hdata.2
    (A.lower_extension_weak_partial hce) (by
      intro a ha
      obtain ⟨rho, hrho, hlarge, K, hK, beta, hbeta, hgrowth⟩ :=
        A.lower_local_column_power_growth g he hei hread hc0 hc0P
          Q hQ hpos hC hcoercive hmin a ha
      exact ⟨rho, hrho, hlarge, K, hK, beta, hbeta,
        fun i b hb r hr => hgrowth b hb r hr i⟩)
  obtain ⟨F, hF, hFae, -⟩ := m64ClosedEmbedding_continuous_representative hei
    m64AnnulusLowerDomain_isOpen A.lowerExtensionMap U hU hUae
  have hboundary : Continuous (fun p : LoopPlane => c0 (p 0)) :=
    hc0.continuous.comp (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous
  have hFeq : EqOn F (fun p : LoopPlane => c0 (p 0)) L := by
    apply Measure.eqOn_open_of_ae_eq (μ := volume) ?_ m64AnnulusLowerStrip_isOpen
      (hF.mono m64AnnulusLower_strip_subset) hboundary.continuousOn
    filter_upwards [ae_restrict_of_ae_restrict_of_subset m64AnnulusLower_strip_subset hFae,
      ae_restrict_mem m64AnnulusLowerStrip_isOpen.measurableSet] with p hp hpL
    rw [hp, lowerExtensionMap, m64AnnulusLowerExtend_left _ _ hpL]
    simp only [m64AnnulusRadialTranslation, annulusPoint, PiLp.add_apply,
      Matrix.cons_val_zero, zero_add]
  refine ⟨F, hF, hFae, ?_⟩
  intro x hx
  have hpoint : annulusPoint x 0 ∈ O :=
    ⟨hx.1, hx.2, by norm_num [annulusPoint], by norm_num [annulusPoint]⟩
  have : (𝓝[L] (annulusPoint x 0)).NeBot :=
    mem_closure_iff_clusterPt.mp (lower_edge_mem_closure hx)
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hF _ hpoint).mono m64AnnulusLower_strip_subset)
    hboundary.continuousAt.continuousWithinAt
    (hFeq.eventuallyEq_of_mem self_mem_nhdsWithin)

end PoincareConjecture.M64ObservedWeakAnnulus
