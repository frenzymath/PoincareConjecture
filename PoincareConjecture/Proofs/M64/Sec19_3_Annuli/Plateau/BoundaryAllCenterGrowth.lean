import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialInteriorGrowth
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialBallGeometry
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.MorreyPowerWeakening










noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "O" => m64AnnulusLowerDomain





theorem m64Boundary_window_closedBall {x0 width : ℝ}
    (hw : 0 < width) (hx : width < x0) (hP : x0 + width < curvePeriod) (hw1 : width < 1) :
    closedBall (annulusPoint x0 0) (width / 2) ⊆ O := by
  intro p hp
  have h0 := (m64LoopPlane_coordinate_dist_le p (annulusPoint x0 0) 0).trans
    (mem_closedBall.mp hp)
  have h1 := (m64LoopPlane_coordinate_dist_le p (annulusPoint x0 0) 1).trans
    (mem_closedBall.mp hp)
  change |p 0 - x0| ≤ width / 2 at h0
  change |p 1 - 0| ≤ width / 2 at h1
  rw [sub_zero] at h1
  obtain ⟨h0l, h0r⟩ := abs_le.mp h0
  obtain ⟨h1l, h1r⟩ := abs_le.mp h1
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩





theorem m64Boundary_all_center_power
    (F : LoopPlane → ℝ) (hF : IntegrableOn F S) (hFpos : ∀ p, 0 ≤ F p)
    {x0 width beta K0 q : ℝ} (hw : 0 < width) (hx : width < x0)
    (hP : x0 + width < curvePeriod) (hw1 : width < 1)
    (hbeta : 0 < beta) (hK0 : 0 ≤ K0) (hq : 0 < q) (hq1 : q < 1)
    (hedge : ∀ x ∈ Icc (x0 - width) (x0 + width), ∀ r ∈ Ioc (0 : ℝ) width,
      (∫ p in closedBall (annulusPoint x 0) r ∩ S, F p) ≤ K0 * r ^ beta)
    (hcontract : ∀ (b : LoopPlane) (r : ℝ), 0 < r → closedBall b r ⊆ S →
      (∫ p in closedBall b (r * Real.exp (-1)), F p) ≤ q * ∫ p in closedBall b r, F p) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ b ∈ closedBall (annulusPoint x0 0) (width / 8), ∀ r ∈ Ioc (0 : ℝ) (width / 8),
        (∫ p in closedBall b r ∩ S, F p) ≤ K * r ^ gamma := by
  let E := fun (b : LoopPlane) (r : ℝ) => ∫ p in closedBall b r ∩ S, F p
  let gamma := min beta (-Real.log q)
  have hgamma : 0 < gamma := lt_min hbeta (neg_pos.mpr (Real.log_neg hq hq1))
  have hgbeta : gamma ≤ beta := min_le_left _ _
  have hgq : gamma ≤ -Real.log q := min_le_right _ _
  let Kedge := K0 * width ^ (beta - gamma)
  have hKedge : 0 ≤ Kedge := by dsimp only [Kedge]; positivity
  have hedgepower (x : ℝ) (hxI : x ∈ Icc (x0 - width) (x0 + width))
      (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) width) :
      E (annulusPoint x 0) r ≤ Kedge * r ^ gamma :=
    m64Morrey_power_bound_weaken (hedge x hxI r hr) hK0 hw hr.1 hr.2 hgamma hgbeta
  have hcompare {b z : LoopPlane} {r s : ℝ} (hsub : closedBall b r ⊆ closedBall z s) :
      E b r ≤ E z s :=
    setIntegral_mono_set (hF.mono_set inter_subset_right) (ae_of_all _ hFpos)
      (ae_of_all _ (inter_subset_inter_left _ hsub))
  have heq {b : LoopPlane} {r : ℝ} (hball : closedBall b r ⊆ S) :
      E b r = ∫ p in closedBall b r, F p := by
    dsimp only [E]
    rw [inter_eq_left.mpr hball]
  have hO := m64Boundary_window_closedBall hw hx hP hw1
  let Kn := Kedge * (3 : ℝ) ^ gamma
  let Ku := Kedge * (4 : ℝ) ^ gamma / Real.exp (-gamma)
  have hKn : 0 ≤ Kn := by dsimp only [Kn]; positivity
  have hKu : 0 ≤ Ku := by dsimp only [Ku]; positivity
  refine ⟨gamma, hgamma, Kn + Ku, by positivity, ?_⟩
  intro b hba r hr
  let z := annulusPoint (b 0) 0
  have hcoord := (m64LoopPlane_coordinate_dist_le b (annulusPoint x0 0) 0).trans
    (mem_closedBall.mp hba)
  change |b 0 - x0| ≤ width / 8 at hcoord
  have hxI : b 0 ∈ Icc (x0 - width) (x0 + width) := by
    constructor <;> linarith [(abs_le.mp hcoord).1, (abs_le.mp hcoord).2]
  have hheight := (m64RadialAxis_near_edge_center (show (annulusPoint x0 0) 1 = 0 from rfl)
    hba).1
  have hbclosed (s : ℝ) (hs : s ≤ width / 8) : closedBall b s ⊆ O :=
    (closedBall_subset_closedBall' (show s + dist b (annulusPoint x0 0) ≤ width / 2 from by
      linarith [mem_closedBall.mp hba])).trans hO
  have hpow : 0 ≤ r ^ gamma := Real.rpow_nonneg hr.1.le _
  by_cases hnear : |b 1| ≤ 2 * r
  · have hsub : closedBall b r ⊆ closedBall z (3 * r) :=
      closedBall_subset_closedBall' (by rw [m64RadialAxis_dist]; linarith)
    have hn := (hcompare hsub).trans
      (hedgepower (b 0) hxI (3 * r) ⟨by linarith [hr.1], by linarith [hr.2]⟩)
    calc
      _ ≤ Kedge * (3 * r) ^ gamma := hn
      _ = Kn * r ^ gamma := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hr.1.le]
        dsimp only [Kn]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hpow
  · have hfar : 2 * r < |b 1| := lt_of_not_ge hnear
    by_cases hupper : 0 < b 1
    · let s := b 1 / 2
      have hs : 0 < s := half_pos hupper
      have hswidth : s ≤ width / 8 := by
        rw [abs_of_pos hupper] at hheight
        dsimp only [s]
        linarith
      have hrs : r ≤ s := by
        rw [abs_of_pos hupper] at hfar
        dsimp only [s]
        linarith
      have hbs : closedBall b s ⊆ S :=
        m64AnnulusLower_closedBall_upper (hbclosed s hswidth) (half_lt_self hupper)
      have hbase : E b s ≤ Kedge * (4 * s) ^ gamma := by
        apply (hcompare (z := z) (s := 4 * s) ?_).trans
          (hedgepower (b 0) hxI (4 * s) ⟨by positivity, by linarith⟩)
        apply closedBall_subset_closedBall'
        rw [m64RadialAxis_dist, abs_of_pos hupper]
        dsimp only [s]
        linarith
      have hmono : MonotoneOn (E b) (Ioc (0 : ℝ) s) := by
        intro u _ v _ huv
        exact hcompare (closedBall_subset_closedBall huv)
      have hstep (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) s) :
          E b (t * Real.exp (-1)) ≤ q * E b t := by
        have hbt := (closedBall_subset_closedBall ht.2).trans hbs
        have hsmall : closedBall b (t * Real.exp (-1)) ⊆ S :=
          (closedBall_subset_closedBall (mul_le_of_le_one_right ht.1.le
            (Real.exp_le_one_iff.mpr (by norm_num)))).trans hbt
        rw [heq hsmall, heq hbt]
        exact hcontract b t ht.1 hbt
      have hu := m64Morrey_power_of_scaled_initial_bound hs hq hKedge hgamma hgq hmono
        (fun t _ => integral_nonneg hFpos) hbase hstep ⟨hr.1, hrs⟩
      exact hu.trans (mul_le_mul_of_nonneg_right (show Ku ≤ Kn + Ku by linarith) hpow)
    · have hrheight : r < -b 1 := by
        rw [abs_of_nonpos (le_of_not_gt hupper)] at hfar
        linarith [hr.1]
      have hbelow := m64AnnulusLower_closedBall_lower (hbclosed r hr.2) hrheight
      have hempty : closedBall b r ∩ S = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro p hp
        exact lt_asymm ((m64AnnulusLowerStrip_coordinates p).mp (hbelow hp.1)).2.2.2
          ((m64AnnulusInterior_coordinates p).mp hp.2).2.2.1
      rw [hempty, setIntegral_empty]
      positivity

end PoincareConjecture
