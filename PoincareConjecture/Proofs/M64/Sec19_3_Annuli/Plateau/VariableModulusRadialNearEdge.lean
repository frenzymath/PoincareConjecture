import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusRadialPowerGrowth
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialInteriorGrowth
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialSmoothGrowth
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialBallGeometry
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyPowerWeakening
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusGrowth













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

omit [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [T2Space M] in
private theorem lowerDiskEnergy_eq_diskEnergy
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) {a : LoopPlane} {r : ℝ}
    (hball : ball a r ⊆ S) : A.lowerDiskEnergy Q a r = A.diskEnergy Q a r := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
  simp only [lowerEnergyDensity, lowerExtensionMap, lowerExtensionColumn,
    m64AnnulusLowerExtend_right _ _ (hball hp)]

set_option maxHeartbeats 1600000 in




theorem weighted_lower_near_edge_column_power_growth
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0)
    (hc0P : Function.Periodic c0 curvePeriod)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hpos : ∀ q v, 0 ≤ Q q v v) {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus)
    {a : LoopPlane} (ha : a ∈ O) (ha0 : a 1 = 0) :
    ∃ rho : ℝ, 0 < rho ∧ closedBall a (2 * rho) ⊆ O ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∃ gamma : ℝ, 0 < gamma ∧
        ∀ b ∈ closedBall a rho, ∀ r ∈ Ioc (0 : ℝ) rho, ∀ i : Fin 2,
          (∫ p in ball b r, ‖A.lowerExtensionColumn i p‖ ^ 2) ≤ K * r ^ gamma := by
  obtain ⟨rho0, hrho0, hedge⟩ := A.weighted_lower_uniform_energy_power_growth
    g he hei hread hc0 hc0P Q hQ hpos hC hcoercive hmodulus hmin
  obtain ⟨q, hq, hq1, hcontract⟩ :=
    A.weighted_energy_contraction g he hei hread Q hQ hpos hC hcoercive hmodulus hmin
  obtain ⟨delta, hdelta, hdeltaO⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (m64AnnulusLowerDomain_isOpen.mem_nhds ha)
  let R := min (delta / 4) (rho0 / 2)
  have hR : 0 < R := by dsimp [R]; positivity
  have hRdelta : R ≤ delta / 4 := min_le_left _ _
  have hRrho : R ≤ rho0 := (min_le_right _ _).trans (half_le_self hrho0.le)
  obtain ⟨beta, hbeta, K0, hK0, hpower⟩ := hedge R ⟨hR, hRrho⟩
  let gamma := min beta (min (-Real.log q) 2)
  have hgamma : 0 < gamma := lt_min hbeta
    (lt_min (neg_pos.mpr (Real.log_neg hq hq1)) (by norm_num))
  have hgbeta : gamma ≤ beta := min_le_left _ _
  have hgq : gamma ≤ -Real.log q :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hg2 : gamma ≤ 2 := (min_le_right _ _).trans (min_le_right _ _)
  let Kedge := K0 * R ^ (beta - gamma)
  have hKedge : 0 ≤ Kedge := by dsimp [Kedge]; positivity
  have hedgepower (z : LoopPlane) (hz : z 1 = 0) (hzo : closedBall z R ⊆ O)
      (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) R) :
      A.lowerDiskEnergy Q z s ≤ Kedge * s ^ gamma :=
    m64Morrey_power_bound_weaken (hpower z hz hzo s hs) hK0 hR hs.1 hs.2 hgamma hgbeta
  have hce : ContDiff ℝ 1 (e ∘ c0) := contMDiff_iff_contDiff.mp (he.comp hc0)
  have hbounded : Bornology.IsBounded (range Q) := (isCompact_range hQ).isBounded
  obtain ⟨B, hB⟩ := hbounded.exists_norm_le
  have hb (p : M) : ‖Q p‖ ≤ B := hB _ (mem_range_self p)
  have hEint := A.lower_energy_integrable hce Q hQ hei.isEmbedding hb
  have hcompare {b z : LoopPlane} {r s : ℝ}
      (hsub : ball b r ⊆ ball z s) (hso : ball z s ⊆ O) :
      A.lowerDiskEnergy Q b r ≤ A.lowerDiskEnergy Q z s :=
    setIntegral_mono_set (hEint.mono_set hso)
      (Eventually.of_forall (A.lowerEnergyDensity_nonneg Q hpos))
      (Eventually.of_forall hsub)
  obtain ⟨D, hD, hDbound⟩ := A.lower_extension_column_bound he hc0 hc0P
  let rho := R / 8
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hrhoR : rho ≤ R := by dsimp [rho]; linarith
  have hlarge : closedBall a (2 * rho) ⊆ O :=
    (closedBall_subset_closedBall (show 2 * rho ≤ delta from by dsimp [rho]; linarith)).trans
      hdeltaO
  let Kn := 2 * C * (Kedge * (3 : ℝ) ^ gamma)
  let Ku := 2 * C * (Kedge * (4 : ℝ) ^ gamma / Real.exp (-gamma))
  let Kl := (Real.pi * D ^ 2) * R ^ ((2 : ℝ) - gamma)
  have hKn : 0 ≤ Kn := by dsimp [Kn]; positivity
  have hKu : 0 ≤ Ku := by dsimp [Ku]; positivity
  have hKl : 0 ≤ Kl := by dsimp [Kl]; positivity
  refine ⟨rho, hrho, hlarge, Kn + Ku + Kl, by positivity, gamma, hgamma, ?_⟩
  intro b hba r hr i
  let z := annulusPoint (b 0) 0
  have hz0 : z 1 = 0 := by simp [z, annulusPoint]
  obtain ⟨hheight, hza⟩ := m64RadialAxis_near_edge_center ha0 hba
  have hzo : closedBall z R ⊆ O :=
    (closedBall_subset_closedBall' (show R + dist z a ≤ delta from by
      dsimp only [z] at *
      dsimp only [rho] at hza
      linarith)).trans hdeltaO
  have hbclosed (s : ℝ) (hs : s ≤ rho) : closedBall b s ⊆ O :=
    (closedBall_subset_closedBall' (show s + dist b a ≤ 2 * rho from by
      linarith [mem_closedBall.mp hba])).trans hlarge
  have hbro : ball b r ⊆ O := ball_subset_closedBall.trans (hbclosed r hr.2)
  have hcol : (∫ p in ball b r, ‖A.lowerExtensionColumn i p‖ ^ 2) ≤
      2 * C * A.lowerDiskEnergy Q b r :=
    A.lower_column_disk_energy_le he hc0 Q hQ hei.isEmbedding hb hpos hC hcoercive b r hbro i
  by_cases hnear : |b 1| ≤ 2 * r
  · have hsR : 3 * r ≤ R := by dsimp [rho] at hr; linarith [hr.2]
    have hsub : ball b r ⊆ ball z (3 * r) :=
      ball_subset_ball' (by rw [m64RadialAxis_dist]; linarith)
    have hso : ball z (3 * r) ⊆ O :=
      ball_subset_closedBall.trans ((closedBall_subset_closedBall hsR).trans hzo)
    have hn := (hcompare hsub hso).trans
      (hedgepower z hz0 hzo (3 * r) ⟨by linarith [hr.1], hsR⟩)
    calc
      _ ≤ 2 * C * (Kedge * (3 * r) ^ gamma) :=
        hcol.trans (mul_le_mul_of_nonneg_left hn (by positivity))
      _ = Kn * r ^ gamma := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hr.1.le]
        dsimp [Kn]
        ring
      _ ≤ (Kn + Ku + Kl) * r ^ gamma :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hr.1.le _)
  · have hfar : 2 * r < |b 1| := lt_of_not_ge hnear
    by_cases hupper : 0 < b 1
    · let s := b 1 / 2
      have hs : 0 < s := half_pos hupper
      have hsheight : s < b 1 := half_lt_self hupper
      have hsRho : s ≤ rho := by
        rw [abs_of_pos hupper] at hheight
        dsimp [s]
        linarith
      have hrs : r ≤ s := by
        rw [abs_of_pos hupper] at hfar
        dsimp [s]
        linarith
      have hbs : closedBall b s ⊆ S :=
        m64AnnulusLower_closedBall_upper (hbclosed s hsRho) hsheight
      have hbs' (t : ℝ) (ht : t ≤ s) : ball b t ⊆ S :=
        ball_subset_closedBall.trans ((closedBall_subset_closedBall ht).trans hbs)
      have h4R : 4 * s ≤ R := by dsimp [rho] at hsRho; linarith
      have hbase : A.diskEnergy Q b s ≤ Kedge * (4 * s) ^ gamma := by
        rw [← lowerDiskEnergy_eq_diskEnergy A Q (hbs' s le_rfl)]
        have hsub : ball b s ⊆ ball z (4 * s) := by
          apply ball_subset_ball'
          rw [m64RadialAxis_dist, abs_of_pos hupper]
          dsimp [s]
          linarith
        exact (hcompare hsub (ball_subset_closedBall.trans
          ((closedBall_subset_closedBall h4R).trans hzo))).trans
          (hedgepower z hz0 hzo (4 * s) ⟨by positivity, h4R⟩)
      have hmono : MonotoneOn (A.diskEnergy Q b) (Ioc (0 : ℝ) s) := by
        intro x hx y hy hxy
        exact A.diskEnergy_mono Q hQ hei.isEmbedding hb hpos b hxy (hbs' y hy.2)
      have hstep (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) s) :
          A.diskEnergy Q b (t * Real.exp (-1)) ≤ q * A.diskEnergy Q b t :=
        hcontract b t ht.1 ((closedBall_subset_closedBall ht.2).trans hbs)
      have hu := m64Morrey_power_of_scaled_initial_bound hs hq hKedge hgamma hgq
        hmono (fun t _ => A.diskEnergy_nonneg Q hpos b t) hbase hstep ⟨hr.1, hrs⟩
      rw [lowerDiskEnergy_eq_diskEnergy A Q (hbs' r hrs)] at hcol
      calc
        _ ≤ 2 * C * ((Kedge * (4 : ℝ) ^ gamma / Real.exp (-gamma)) * r ^ gamma) :=
          hcol.trans (mul_le_mul_of_nonneg_left hu (by positivity))
        _ = Ku * r ^ gamma := by dsimp [Ku]; ring
        _ ≤ (Kn + Ku + Kl) * r ^ gamma :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hr.1.le _)
    · have hbneg : b 1 ≤ 0 := le_of_not_gt hupper
      have hrheight : r < -b 1 := by
        rw [abs_of_nonpos hbneg] at hfar
        linarith [hr.1]
      have hbl : ball b r ⊆ m64AnnulusLowerStrip :=
        ball_subset_closedBall.trans
          (m64AnnulusLower_closedBall_lower (hbclosed r hr.2) hrheight)
      have hLp := ((A.lower_extension_memLp hce).2 i).mono_measure
        (Measure.restrict_mono hbro le_rfl)
      have hint := (memLp_two_iff_integrable_sq_norm hLp.aestronglyMeasurable).mp hLp
      have hquad : (∫ p in ball b r, ‖A.lowerExtensionColumn i p‖ ^ 2) ≤
          (Real.pi * D ^ 2) * r ^ (2 : ℝ) := by
        calc
          _ ≤ ∫ _ in ball b r, D ^ 2 := by
            apply integral_mono_ae hint integrableOn_const
            filter_upwards [ae_restrict_mem measurableSet_ball] with p hp
            exact (sq_le_sq₀ (norm_nonneg _) hD).mpr
              (hDbound p (hbro hp)
                (((m64AnnulusLowerStrip_coordinates p).mp (hbl hp)).2.2.2) i)
          _ = _ := by
            rw [setIntegral_const, smul_eq_mul, Measure.real, EuclideanSpace.volume_ball_fin_two]
            simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, Real.rpow_two,
              ENNReal.toReal_ofReal hr.1.le, ENNReal.toReal_ofReal Real.pi_pos.le]
            ring
      have hl := m64Morrey_power_bound_weaken hquad (by positivity) hR hr.1
        (hr.2.trans hrhoR) hgamma hg2
      exact hl.trans (mul_le_mul_of_nonneg_right
        (show Kl ≤ Kn + Ku + Kl from by linarith) (Real.rpow_nonneg hr.1.le _))

end PoincareConjecture.M64ObservedWeakAnnulus
