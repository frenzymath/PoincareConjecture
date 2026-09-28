import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Embedding.MorreyHigherOrder
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Iterated.Multiply
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Embedding.ExponentIteration
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Representative

noncomputable section

open MeasureTheory Set Filter Topology Metric Function
open scoped ENNReal NNReal ContDiff

namespace Poincare
namespace Analysis
namespace Sobolev
namespace EuclideanIteratedEmbedding

open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding

variable {d : ℕ} [NeZero d]

local notation "EuN" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem exists_cutoff_ball
    {x₀ : EuN} {R : ℝ} (hR : 0 < R) :
    ∃ χ : EuN → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      HasCompactSupport χ ∧
      Set.range χ ⊆ Set.Icc (0 : ℝ) 1 ∧
      (∀ x ∈ Metric.closedBall x₀ R, χ x = 1) ∧
      tsupport χ ⊆ Metric.closedBall x₀ (3 * R / 2) := by
  classical
  have hδ_pos : (0 : ℝ) < R / 4 := by linarith
  have hclosed : IsClosed (Metric.closedBall x₀ R) := Metric.isClosed_closedBall
  have hopen_thick :
      IsOpen (Metric.thickening (R / 4) (Metric.closedBall x₀ R)) :=
    isOpen_thickening
  have hsub : Metric.closedBall x₀ R ⊆
      Metric.thickening (R / 4) (Metric.closedBall x₀ R) :=
    Metric.self_subset_thickening hδ_pos _
  rcases exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ EuN)
      (s := Metric.thickening (R / 4) (Metric.closedBall x₀ R))
      (t := Metric.closedBall x₀ R)
      hopen_thick hclosed hsub with
    ⟨χ, hχ_smooth, hχ_range, hχ_support, hχ_one_iff⟩
  have h_supp_in_closedBall :
      tsupport χ ⊆ Metric.closedBall x₀ (3 * R / 2) := by
    have h_closed : IsClosed (Metric.closedBall x₀ (3 * R / 2)) :=
      Metric.isClosed_closedBall
    rw [tsupport, hχ_support]
    refine closure_minimal ?_ h_closed
    intro y hy
    rw [Metric.mem_thickening_iff] at hy
    rcases hy with ⟨z, hz_mem, hyz⟩
    rw [Metric.mem_closedBall] at hz_mem ⊢
    calc dist y x₀ ≤ dist y z + dist z x₀ := dist_triangle _ _ _
      _ ≤ R / 4 + R := by
          have hyz_le : dist y z ≤ R / 4 := le_of_lt hyz
          linarith
      _ ≤ 3 * R / 2 := by linarith
  refine ⟨χ, contMDiff_iff_contDiff.mp hχ_smooth, ?_, hχ_range, ?_,
    h_supp_in_closedBall⟩
  · refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (x := x₀) (3 * R / 2)) ?_
    exact (subset_tsupport _).trans h_supp_in_closedBall
  · intro x hx
    exact (hχ_one_iff x).1 hx

omit [NeZero d] in
private lemma exists_uniform_iteratedFDeriv_bound
    {χ : EuN → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ_compact : HasCompactSupport χ)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ m, ∀ x : EuN, ‖iteratedFDeriv ℝ j χ x‖ ≤ C := by
  classical
  have h_per_j : ∀ j, ∃ Cj : ℝ, 0 ≤ Cj ∧
      ∀ x : EuN, ‖iteratedFDeriv ℝ j χ x‖ ≤ Cj := by
    intro j
    have h_cont : Continuous (fun x : EuN => iteratedFDeriv ℝ j χ x) :=
      hχ.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    have h_supp : HasCompactSupport (fun x : EuN => iteratedFDeriv ℝ j χ x) :=
      hχ_compact.iteratedFDeriv (𝕜 := ℝ) j
    obtain ⟨Mj, hMj⟩ := h_supp.exists_bound_of_continuous h_cont
    exact ⟨max 0 Mj, le_max_left _ _, fun x => (hMj x).trans (le_max_right _ _)⟩
  let Cj : ℕ → ℝ := fun j => Classical.choose (h_per_j j)
  have hCj_nn : ∀ j, 0 ≤ Cj j := fun j => (Classical.choose_spec (h_per_j j)).1
  have hCj_bound : ∀ j, ∀ x : EuN, ‖iteratedFDeriv ℝ j χ x‖ ≤ Cj j := fun j =>
    (Classical.choose_spec (h_per_j j)).2
  have h_nonempty : (Finset.range (m + 1)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩
  let C : ℝ := (Finset.range (m + 1)).sup' h_nonempty Cj
  have hC_ge : ∀ j ∈ Finset.range (m + 1), Cj j ≤ C := fun j hj =>
    Finset.le_sup' Cj hj
  refine ⟨C, le_trans (hCj_nn 0)
    (hC_ge 0 (Finset.mem_range.mpr (Nat.zero_lt_succ _))), ?_⟩
  intro j hj x
  exact le_trans (hCj_bound j x)
    (hC_ge j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))

omit [NeZero d] in
private lemma cutoff_memWkp_two
    {x₀ : EuN} {R : ℝ} (hR : 0 < R)
    {χ : EuN → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ_compact : HasCompactSupport χ)
    {u : EuN → ℝ} {Ω : Set EuN}
    (hball : Metric.ball x₀ (2 * R) ⊆ Ω)
    {k : ℕ} (hu : MemWkp (d := d) k 2 u Ω) :
    MemWkp (d := d) k 2 (fun x => χ x * u x) (Metric.ball x₀ (2 * R)) := by
  have h2R_pos : (0 : ℝ) < 2 * R := by linarith
  have hball_open : IsOpen (Metric.ball x₀ (2 * R)) := Metric.isOpen_ball
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hu_ball : MemWkp (d := d) k 2 u (Metric.ball x₀ (2 * R)) :=
    MemWkp.mono_set (d := d) hp_one hball_open hball hu
  obtain ⟨C, _hC_nn, hC_bound⟩ :=
    exists_uniform_iteratedFDeriv_bound (d := d) hχ hχ_compact k
  have hχ_bound : ∀ j ≤ k, ∀ x ∈ Metric.ball x₀ (2 * R),
      ‖iteratedFDeriv ℝ j χ x‖ ≤ C := fun j hj x _ => hC_bound j hj x
  exact MemWkp.smul_smooth_bounded (d := d) k hp_one hball_open hχ hχ_bound hu_ball

private theorem tower_to_supercritical
    {Ω : Set EuN} (hΩ_open : IsOpen Ω) (m : ℕ) :
    ∀ (s : ℕ) {p : ℝ}, 1 ≤ p →
      RegularExponent.IsRegular (d : ℝ) p (s + 1) →
      (d : ℝ) < ((s + 1 : ℕ) : ℝ) * p →
      ∀ {f : EuN → ℝ}, HasCompactSupport f → tsupport f ⊆ Ω →
        MemWkp (d := d) (m + 1 + s) (ENNReal.ofReal p) f Ω →
          ∃ q : ℝ, 1 ≤ q ∧ (d : ℝ) < q ∧
            MemWkp (d := d) (m + 1) (ENNReal.ofReal q) f Ω := by
  intro s
  induction s with
  | zero =>
      intro p hp_one _hreg hkp f _hf_cpt _hf_supp hf
      have hp_dim : (d : ℝ) < p := by
        have : ((0 + 1 : ℕ) : ℝ) = 1 := by norm_num
        rw [this, one_mul] at hkp
        exact hkp
      exact ⟨p, hp_one, hp_dim, by simpa using hf⟩
  | succ s ih =>
      intro p hp_one hreg hkp f hf_cpt hf_supp hf
      have hp_ne_d : p ≠ (d : ℝ) := hreg.p_ne_n_of_one_le (by omega)
      rcases lt_or_gt_of_ne hp_ne_d with hp_lt | hp_gt
      · have hp_pos : 0 < p := by linarith
        have hf' : MemWkp (d := d) ((m + 1 + s) + 1) (ENNReal.ofReal p) f Ω := by
          have h_idx : m + 1 + (s + 1) = (m + 1 + s) + 1 := by ring
          rw [h_idx] at hf
          exact hf
        obtain ⟨h_mem_p1, _h_norm_p1⟩ :=
          TowerStep.MemWkp_subcritical_iterated (d := d) (m + 1 + s)
            hp_one hp_lt hΩ_open hf_cpt hf_supp hf'
        set p_1 : ℝ := (d : ℝ) * p / ((d : ℝ) - p) with hp_1_def
        have hd_pos : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
        have hd_p_pos : 0 < (d : ℝ) - p := by linarith
        have hp_1_ge_p : p ≤ p_1 := by
          rw [hp_1_def, le_div_iff₀ hd_p_pos]
          nlinarith [hp_pos]
        have hp_1_one : 1 ≤ p_1 := le_trans hp_one hp_1_ge_p
        have hkp_next : (d : ℝ) < ((s + 1 : ℕ) : ℝ) * p_1 := by
          have h_form : (d : ℝ) < ((s + 1 : ℕ) + 1 : ℝ) * p := by
            have hkp_cast : ((s + 1 + 1 : ℕ) : ℝ) * p =
                ((s + 1 : ℕ) + 1 : ℝ) * p := by push_cast; ring
            rw [hkp_cast] at hkp
            exact hkp
          have h_id :=
            IterationCalc.kp1_real_gt_d_of_kp1p_gt_d d (s + 1) p hp_pos hp_lt h_form
          rw [hp_1_def]
          exact h_id
        have hreg_p_1 : RegularExponent.IsRegular (d : ℝ) p_1 (s + 1) := by
          rw [hp_1_def]
          exact hreg.tower_step hp_one hp_lt
        have h_mem_p1' : MemWkp (d := d) (m + 1 + s) (ENNReal.ofReal p_1) f Ω := by
          rw [hp_1_def]; exact h_mem_p1
        exact ih hp_1_one hreg_p_1 hkp_next hf_cpt hf_supp h_mem_p1'
      · exact ⟨p, hp_one, hp_gt, MemWkp.le_of_le (by omega) hf⟩

private theorem exists_contDiff_m_rep_ball
    {x₀ : EuN} {R : ℝ} (hR : 0 < R)
    {u : EuN → ℝ} {Ω : Set EuN}
    (hball : Metric.ball x₀ (2 * R) ⊆ Ω)
    (m : ℕ) (hu : MemWkp (d := d) (m + 1 + d) 2 u Ω) :
    ∃ f : EuN → ℝ,
      ContDiff ℝ m f ∧
      u =ᵐ[volume.restrict (Metric.ball x₀ (R / 2))] f := by
  classical
  have h2R_pos : (0 : ℝ) < 2 * R := by linarith
  have hball_open : IsOpen (Metric.ball x₀ (2 * R)) := Metric.isOpen_ball
  have hd_pos : 0 < d := NeZero.pos d
  have hd_real_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
  obtain ⟨χ, hχ_smooth, hχ_cpt, _hχ_range, hχ_one, hχ_supp⟩ :=
    exists_cutoff_ball (d := d) hR
  set v : EuN → ℝ := fun x => χ x * u x with hv_def
  have hv_memWkp : MemWkp (d := d) (m + 1 + d) 2 v (Metric.ball x₀ (2 * R)) :=
    cutoff_memWkp_two (d := d) hR hχ_smooth hχ_cpt hball hu
  have h_supp_subset : Function.support v ⊆ Function.support χ := by
    intro x hx
    have hvx : v x ≠ 0 := hx
    intro hχx
    exact hvx (by simp [hv_def, hχx])
  have hv_supp_subset_χ : tsupport v ⊆ tsupport χ := closure_mono h_supp_subset
  have hv_supp_closed : tsupport v ⊆ Metric.closedBall x₀ (3 * R / 2) :=
    hv_supp_subset_χ.trans hχ_supp
  have hcball_subset_ball :
      Metric.closedBall x₀ (3 * R / 2) ⊆ Metric.ball x₀ (2 * R) := by
    intro y hy
    rw [Metric.mem_closedBall] at hy
    rw [Metric.mem_ball]
    linarith
  have hv_supp_ball : tsupport v ⊆ Metric.ball x₀ (2 * R) :=
    hv_supp_closed.trans hcball_subset_ball
  have hv_cpt : HasCompactSupport v :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (x := x₀) (3 * R / 2))
      ((subset_tsupport _).trans hv_supp_closed)
  have hs_max_succ_pos : 1 ≤ d + 1 := by omega
  have hp_2_strict : (1 : ℝ) < 2 := by norm_num
  have h_d_lt_kp_2 : (d : ℝ) < ((d + 1 : ℕ) : ℝ) * 2 := by
    have heq : ((d + 1 : ℕ) : ℝ) * 2 = (2 * (d + 1) : ℕ) := by
      push_cast; ring
    rw [heq]
    have : (d : ℝ) < (2 * (d + 1) : ℕ) := by
      push_cast; linarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d]
    exact this
  obtain ⟨p₀, hp₀_one, hp₀_lt, h_d_lt_kp₀, hp₀_reg⟩ :=
    RegularExponent.exists_regular_exponent_below
      (d : ℝ) (d + 1) hs_max_succ_pos hp_2_strict h_d_lt_kp_2
  have hv_mem_two : MemWkp (d := d) (m + 1 + d) 2 v
      (Metric.ball x₀ (2 * R)) := hv_memWkp
  have hp₀_le_two_enn : ENNReal.ofReal p₀ ≤ (2 : ℝ≥0∞) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.ofReal_natCast]; rfl]
    exact ENNReal.ofReal_le_ofReal hp₀_lt.le
  have hp₀_one_enn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p₀ := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
    exact ENNReal.ofReal_le_ofReal hp₀_one
  have hv_mem_p₀ : MemWkp (d := d) (m + 1 + d) (ENNReal.ofReal p₀) v
      (Metric.ball x₀ (2 * R)) :=
    EuclideanIteratedMonoExp.memWkp_mono_exponent_of_tsupport_subset (d := d)
      (m + 1 + d) hball_open Metric.isClosed_closedBall
      ((measure_closedBall_lt_top (x := x₀) (r := 3 * R / 2)).ne)
      hp₀_one_enn hp₀_le_two_enn hv_supp_closed hv_mem_two
  obtain ⟨q, _hq_one, hq_dim, hv_mem_q⟩ :=
    tower_to_supercritical (d := d) hball_open m d hp₀_one hp₀_reg
      h_d_lt_kp₀ hv_cpt hv_supp_ball hv_mem_p₀
  obtain ⟨f, hf_cdiff, hf_ae⟩ :=
    EuclideanMorrey.morrey_iteratedFDeriv_representative (d := d) (p := q)
      (x₀ := x₀) (R := 2 * R) (u := v) hq_dim h2R_pos m hv_mem_q
  refine ⟨f, hf_cdiff, ?_⟩
  have h_ball_eq : Metric.ball x₀ (2 * R / 4) = Metric.ball x₀ (R / 2) := by
    congr 1; ring
  have hu_eq_v : u =ᵐ[volume.restrict (Metric.ball x₀ (R / 2))] v := by
    refine (ae_restrict_iff' (Metric.isOpen_ball.measurableSet)).mpr ?_
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    have hx_closed : x ∈ Metric.closedBall x₀ R := by
      rw [Metric.mem_ball] at hx
      rw [Metric.mem_closedBall]
      linarith
    simp only [hv_def, hχ_one x hx_closed, one_mul]
  have hv_eq_f : v =ᵐ[volume.restrict (Metric.ball x₀ (R / 2))] f := by
    rw [← h_ball_eq]
    exact hf_ae
  exact hu_eq_v.trans hv_eq_f

private theorem exists_contDiffOn_top_rep_ball
    {x₀ : EuN} {R : ℝ} (hR : 0 < R)
    {u : EuN → ℝ} {Ω : Set EuN}
    (hball : Metric.ball x₀ (2 * R) ⊆ Ω)
    (hu : ∀ k : ℕ, MemWkp (d := d) k 2 u Ω) :
    ∃ f : EuN → ℝ,
      ContDiffOn ℝ (∞ : WithTop ℕ∞) f (Metric.ball x₀ (R / 2)) ∧
      u =ᵐ[volume.restrict (Metric.ball x₀ (R / 2))] f := by
  classical
  have hR2_pos : (0 : ℝ) < R / 2 := by linarith
  have h_ball_open : IsOpen (Metric.ball x₀ (R / 2)) := Metric.isOpen_ball
  obtain ⟨f₀, hf₀_cdiff, hf₀_ae⟩ :=
    exists_contDiff_m_rep_ball (d := d) hR hball 0 (hu _)
  refine ⟨f₀, ?_, hf₀_ae⟩
  rw [contDiffOn_infty]
  intro m
  obtain ⟨fₘ, hfₘ_cdiff, hfₘ_ae⟩ :=
    exists_contDiff_m_rep_ball (d := d) hR hball m (hu _)
  have h_ae_eq : f₀ =ᵐ[volume.restrict (Metric.ball x₀ (R / 2))] fₘ :=
    (hf₀_ae.symm).trans hfₘ_ae
  have h_eqOn : Set.EqOn f₀ fₘ (Metric.ball x₀ (R / 2)) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq h_ae_eq h_ball_open
      hf₀_cdiff.continuous.continuousOn hfₘ_cdiff.continuous.continuousOn
  refine (hfₘ_cdiff.contDiffOn (s := Metric.ball x₀ (R / 2))).congr ?_
  intro x hx
  exact h_eqOn hx

private theorem exists_contDiffOn_top_rep_nhd
    {u : EuN → ℝ} {Ω : Set EuN} (hΩ : IsOpen Ω)
    (hu : ∀ k : ℕ, MemWkp (d := d) k 2 u Ω) {x : EuN} (hx : x ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Ω ∧
      ∃ f : EuN → ℝ,
        ContDiffOn ℝ (∞ : WithTop ℕ∞) f (Metric.ball x r) ∧
        u =ᵐ[volume.restrict (Metric.ball x r)] f := by
  classical
  obtain ⟨ρ, hρ_pos, hρ_subset⟩ := Metric.isOpen_iff.mp hΩ x hx
  set R : ℝ := ρ / 4 with hR_def
  have hR_pos : 0 < R := by rw [hR_def]; linarith
  have hball_subset : Metric.ball x (2 * R) ⊆ Ω := by
    intro y hy
    refine hρ_subset ?_
    rw [Metric.mem_ball] at hy ⊢
    have h2R : 2 * R ≤ ρ := by rw [hR_def]; linarith
    exact lt_of_lt_of_le hy h2R
  obtain ⟨f, hf_cdiff, hf_ae⟩ :=
    exists_contDiffOn_top_rep_ball (d := d) hR_pos hball_subset hu
  exact ⟨R / 2, by linarith, fun y hy => hball_subset (by
    rw [Metric.mem_ball] at hy ⊢; linarith), f, hf_cdiff, hf_ae⟩

theorem contDiffOn_of_forall_memWkp_two
    {u : EuN → ℝ} {Ω : Set EuN} (hΩ : IsOpen Ω)
    (hu : ∀ k : ℕ, MemWkp (d := d) k 2 u Ω) :
    ∃ u_smooth : EuN → ℝ,
      ContDiffOn ℝ (∞ : WithTop ℕ∞) u_smooth Ω ∧
      u =ᵐ[volume.restrict Ω] u_smooth := by
  suffices h : ∃ U : EuN → ℝ, ContDiffOn ℝ ∞ U Ω ∧
      U =ᵐ[volume.restrict Ω] u from
    h.imp fun U hU => ⟨hU.1, hU.2.symm⟩
  apply Poincare.Analysis.Elliptic.exists_smooth_representative_of_local
  intro x hx
  obtain ⟨r, hr, hball, f, hf, hfu⟩ := exists_contDiffOn_top_rep_nhd hΩ hu hx
  exact ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    hball, f, hf, hfu.symm⟩

theorem exists_smooth_representative_of_local_memWkp
    {u : EuN → ℝ} {Ω : Set EuN}
    (hu : ∀ x ∈ Ω, ∃ V : Set EuN,
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ ∀ k : ℕ, MemWkp k 2 u V) :
    ∃ U : EuN → ℝ, ContDiffOn ℝ ∞ U Ω ∧ U =ᵐ[volume.restrict Ω] u := by
  apply Poincare.Analysis.Elliptic.exists_smooth_representative_of_local
  intro x hx
  obtain ⟨V, hV, hxV, hVΩ, huV⟩ := hu x hx
  obtain ⟨f, hf, hfu⟩ := contDiffOn_of_forall_memWkp_two hV huV
  exact ⟨V, hV, hxV, hVΩ, f, hf, hfu.symm⟩

theorem exists_smooth_representative_of_memWkp_locally
    {u : EuN → ℝ} {Ω : Set EuN}
    (hu : ∀ x ∈ Ω, ∀ k : ℕ, ∃ V : Set EuN,
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ MemWkp k 2 u V) :
    ∃ U : EuN → ℝ, ContDiffOn ℝ ∞ U Ω ∧ U =ᵐ[volume.restrict Ω] u := by
  have hrep : ∀ x ∈ Ω, ∀ m : ℕ, ∃ V : Set EuN,
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ ∃ f : EuN → ℝ,
        ContDiff ℝ m f ∧ f =ᵐ[volume.restrict V] u := by
    intro x hx m
    obtain ⟨V, hV, hxV, hVΩ, huV⟩ := hu x hx (m + 1 + d)
    obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.mp hV x hxV
    have hR : 0 < ρ / 4 := by positivity
    have hball : Metric.ball x (2 * (ρ / 4)) ⊆ V := by
      apply Set.Subset.trans (Metric.ball_subset_ball (by linarith)) hρV
    obtain ⟨f, hf, hfu⟩ := exists_contDiff_m_rep_ball hR hball m huV
    refine ⟨Metric.ball x (ρ / 4 / 2), Metric.isOpen_ball,
      Metric.mem_ball_self (by positivity), ?_, f, hf, hfu.symm⟩
    exact ((Metric.ball_subset_ball (by linarith)).trans hball).trans hVΩ
  apply Poincare.Analysis.Elliptic.exists_smooth_representative_of_local
  intro x hx
  obtain ⟨V, hV, hxV, hVΩ, f, hf, hfu⟩ := hrep x hx 0
  refine ⟨V, hV, hxV, hVΩ, f, ?_, hfu⟩
  rw [contDiffOn_infty]
  intro m
  apply contDiffOn_of_locally_contDiffOn
  intro y hy
  obtain ⟨W, hW, hyW, _, g, hg, hgu⟩ := hrep y (hVΩ hy) m
  refine ⟨W, hW, hyW, ?_⟩
  have heq : Set.EqOn f g (V ∩ W) :=
    Poincare.Analysis.Elliptic.eqOn_inter_of_ae_eq hV hW
      hf.continuous.continuousOn hg.continuous.continuousOn hfu hgu
  exact hg.contDiffOn.congr heq

end EuclideanIteratedEmbedding
end Sobolev
end Analysis
end Poincare
