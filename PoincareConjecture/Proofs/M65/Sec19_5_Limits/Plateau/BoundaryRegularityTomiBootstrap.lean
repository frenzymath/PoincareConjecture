import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityTomiIteration










set_option autoImplicit false

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap LineDeriv InnerProductSpace

namespace PoincareConjecture.M65Boundary

open EuclideanTranslationNative

private theorem lower_singular_power {r s a : ℝ}
    (hr : 0 ≤ r) (hs : 0 < s) (hsa : s ≤ a) :
    r ^ (-s) ≤ 1 + r ^ (-a) := by
  by_cases hr0 : r = 0
  · rw [hr0, Real.zero_rpow (neg_ne_zero.mpr hs.ne'),
      Real.zero_rpow (neg_ne_zero.mpr (hs.trans_le hsa).ne')]
    norm_num
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  by_cases hr1 : r ≤ 1
  · exact (Real.rpow_le_rpow_of_exponent_ge hrpos hr1 (neg_le_neg hsa)).trans
      (le_add_of_nonneg_left zero_le_one)
  · exact (Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hr1) (neg_nonpos.mpr hs.le)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hr _))





theorem forcing_weight_of_local_energy
    (E f : LoopPlane → ℝ) (hE : Integrable E) (hE0 : ∀ z, 0 ≤ E z)
    (hf : Integrable f) {U : Set LoopPlane} (hU : MeasurableSet U)
    {C s a ρ : ℝ} (hC : 0 ≤ C) (hs : 0 < s) (hsa : s ≤ a) (hρ : 0 < ρ)
    (hgrowth : ∀ᵐ z ∂volume, z ∈ U → |f z| ≤ C * E z)
    (x : LoopPlane) (hball : closedBall x ρ ⊆ U)
    (hweighted : IntegrableOn (fun z => ‖z - x‖ ^ (-a) * E z) U) :
    Integrable (fun z => |f z| * ‖z - x‖ ^ (-s)) ∧
      (∫ z, |f z| * ‖z - x‖ ^ (-s)) ≤
        C * ((∫ z, E z) + ∫ z in U, ‖z - x‖ ^ (-a) * E z) +
          ρ ^ (-s) * ∫ z, |f z| := by
  let G := fun z => |f z| * ‖z - x‖ ^ (-s)
  let W := fun z => ‖z - x‖ ^ (-a) * E z
  have hG0 (z : LoopPlane) : 0 ≤ G z := by dsimp only [G]; positivity
  have hGm : AEStronglyMeasurable G volume := by
    have hm : Measurable (fun z : LoopPlane => ‖z - x‖ ^ (-s)) := by fun_prop
    simpa +instances only [G, Real.norm_eq_abs] using! hf.norm.1.mul hm.aestronglyMeasurable
  have hloc : ∀ᵐ z ∂volume.restrict U, G z ≤ C * (E z + W z) := by
    filter_upwards [ae_restrict_mem hU, hgrowth.filter_mono ae_restrict_le] with z hzU hz
    calc
      G z ≤ (C * E z) * ‖z - x‖ ^ (-s) :=
        mul_le_mul_of_nonneg_right (hz hzU) (Real.rpow_nonneg (norm_nonneg _) _)
      _ ≤ (C * E z) * (1 + ‖z - x‖ ^ (-a)) :=
        mul_le_mul_of_nonneg_left (lower_singular_power (norm_nonneg _) hs hsa)
          (mul_nonneg hC (hE0 z))
      _ = C * (E z + W z) := by dsimp only [W]; ring
  have hmajor : IntegrableOn (fun z => C * (E z + W z)) U := by
    simpa +instances only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using!
      (hE.integrableOn.add hweighted).const_mul C
  have hlocal : IntegrableOn G U := by
    apply hmajor.mono' hGm.restrict
    filter_upwards [hloc] with z hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hG0 z)] using hz
  have hfar : ∀ᵐ z ∂volume.restrict Uᶜ, G z ≤ ρ ^ (-s) * |f z| := by
    filter_upwards [ae_restrict_mem hU.compl] with z hz
    have hdist : ρ < ‖z - x‖ := by
      have hnot : z ∉ closedBall x ρ := fun h => hz (hball h)
      simpa only [mem_closedBall, dist_eq_norm, not_le] using hnot
    calc
      G z ≤ |f z| * ρ ^ (-s) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hρ hdist.le (neg_nonpos.mpr hs.le)) (abs_nonneg _)
      _ = _ := mul_comm _ _
  have hfi : Integrable (fun z => |f z|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have htail : IntegrableOn G Uᶜ := by
    apply (hfi.const_mul (ρ ^ (-s))).integrableOn.mono' hGm.restrict
    filter_upwards [hfar] with z hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hG0 z)] using hz
  have hglobal : Integrable G := by
    have hi := integrableOn_union.mpr ⟨hlocal, htail⟩
    simpa only [union_compl_self, integrableOn_univ] using hi
  refine ⟨hglobal, ?_⟩
  have hlocalBound : (∫ z in U, G z) ≤ C * ((∫ z, E z) + ∫ z in U, W z) := by
    calc
      _ ≤ ∫ z in U, C * (E z + W z) := integral_mono_ae hlocal hmajor hloc
      _ = C * ((∫ z in U, E z) + ∫ z in U, W z) := by
        rw [integral_const_mul, integral_add hE.integrableOn hweighted]
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
        (setIntegral_le_integral hE (ae_of_all _ hE0)) le_rfl) hC
  have htailBound : (∫ z in Uᶜ, G z) ≤ ρ ^ (-s) * ∫ z, |f z| := by
    calc
      _ ≤ ∫ z in Uᶜ, ρ ^ (-s) * |f z| :=
        integral_mono_ae htail (hfi.const_mul _).integrableOn hfar
      _ = ρ ^ (-s) * ∫ z in Uᶜ, |f z| := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hfi (ae_of_all _ fun z => abs_nonneg (f z)))
          (Real.rpow_nonneg hρ.le _)
  rw [← integral_add_compl hU hglobal]
  exact add_le_add hlocalBound htailBound



def WeightedIntegralNear (F : LoopPlane → ℝ) (p : LoopPlane) (a : ℝ) : Prop :=
  ∃ r > 0, ∃ B ≥ 0, ∀ x ∈ ball p r,
    IntegrableOn (fun z => ‖z - x‖ ^ (-a) * F z) (ball p (2 * r)) ∧
      (∫ z in ball p (2 * r), ‖z - x‖ ^ (-a) * F z) ≤ B

private theorem WeightedIntegralNear.exists_radius
    {F : LoopPlane → ℝ} {p : LoopPlane} {a R : ℝ}
    (hF : ∀ z, 0 ≤ F z) (h : WeightedIntegralNear F p a) (hR : 0 < R) :
    ∃ r > 0, r ≤ R ∧ ∃ B ≥ 0, ∀ x ∈ ball p r,
      IntegrableOn (fun z => ‖z - x‖ ^ (-a) * F z) (ball p (2 * r)) ∧
        (∫ z in ball p (2 * r), ‖z - x‖ ^ (-a) * F z) ≤ B := by
  obtain ⟨r0, hr0, B, hB, hh⟩ := h
  refine ⟨min r0 R, lt_min hr0 hR, min_le_right _ _, B, hB, ?_⟩
  intro x hx
  obtain ⟨hi, hb⟩ := hh x (ball_subset_ball (min_le_left _ _) hx)
  have hsub : ball p (2 * min r0 R) ⊆ ball p (2 * r0) :=
    ball_subset_ball (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
  exact ⟨hi.mono_set hsub, (setIntegral_mono_set hi
    (ae_of_all _ fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hF z))
    hsub.eventuallyLE).trans hb⟩

set_option maxHeartbeats 1400000 in




theorem gradient_weight_of_energy {N : ℕ} (u : Fin N → ScalarL2 2)
    (d : Fin N → Fin 2 → ScalarL2 2) (f : Fin N → LoopPlane → ℝ)
    (hf : ∀ j, Integrable (f j)) {U : Set LoopPlane} (hU : IsOpen U)
    {R : ℝ} (hfs : ∀ j, Function.support (f j) ⊆ closedBall (0 : LoopPlane) R)
    (hweak : ∀ j i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d j i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u j z * fderiv ℝ φ z (EuclideanSpace.single i 1)))
    (heq : ∀ j (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f j z * φ z))
    {C a s : ℝ} (hC : 0 ≤ C) (hs : 0 < s) (hs1 : s < 1) (hsa : s ≤ a)
    (hgrowth : ∀ j, ∀ᵐ z ∂volume, z ∈ U →
      |f j z| ≤ C * (∑ k : Fin N, ∑ i : Fin 2, (d k i z) ^ 2))
    {p : LoopPlane} (hp : p ∈ U)
    (henergy : WeightedIntegralNear (fun z => ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) p a) :
    WeightedIntegralNear (fun z => ∑ j : Fin N, ∑ i : Fin 2, |d j i z|) p (s + 1) := by
  classical
  let E := fun z => ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2
  have hE : Integrable E := integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun i _ => (Lp.memLp (d j i)).integrable_sq
  have hE0 (z : LoopPlane) : 0 ≤ E z := by dsimp only [E]; positivity
  obtain ⟨R0, hR0, hR0U⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp)
  obtain ⟨r0, hr0, hrR, B, hB, henergy0⟩ :=
    henergy.exists_radius hE0 (show 0 < R0 / 4 by positivity)
  have hU0 : ball p (2 * r0) ⊆ U :=
    ball_subset_closedBall.trans
      ((closedBall_subset_closedBall (by linarith)).trans hR0U)
  have hb : 1 < s + 1 := by linarith
  have hb2 : s + 1 < 2 := by linarith
  choose rj hrj _hsubj Aj hAj Cj hCj hgrad using fun j : Fin N =>
    plane_weighted_gradient_estimate hb hb2 (u j) (d j) (f j) (hf j) hU (hfs j)
      (hweak j) (heq j) hp
  let radii : Finset ℝ := insert r0 (Finset.univ.image rj)
  have hne : radii.Nonempty := ⟨r0, Finset.mem_insert_self _ _⟩
  have hpos : ∀ q ∈ radii, 0 < q := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hr0
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    exact hrj j
  let r := radii.min' hne / 4
  have hr : 0 < r := by dsimp only [r]; exact div_pos (hpos _ (Finset.min'_mem _ _)) (by norm_num)
  have hrr0 : r ≤ r0 := by
    have hh := Finset.min'_le radii r0 (Finset.mem_insert_self _ _)
    dsimp only [r]
    linarith
  have hrrj (j : Fin N) : 2 * r ≤ rj j := by
    have hh := Finset.min'_le radii (rj j) (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
    dsimp only [r]
    linarith [hrj j]
  let Fj := fun j : Fin N => C * ((∫ z, E z) + B) + (r0 / 2) ^ (-s) * ∫ z, |f j z|
  have hFj (j : Fin N) : 0 ≤ Fj j := by
    have hi : 0 ≤ ∫ z, E z := integral_nonneg hE0
    have hf0 : 0 ≤ ∫ z, |f j z| := integral_nonneg fun z => abs_nonneg _
    dsimp only [Fj]
    positivity
  let A := ∑ j : Fin N, (Aj j + Cj j * Fj j)
  have hA : 0 ≤ A := Finset.sum_nonneg fun j _ =>
    add_nonneg (hAj j) (mul_nonneg (hCj j).le (hFj j))
  refine ⟨r, hr, A, hA, ?_⟩
  intro x hx
  have hx0 : x ∈ ball p r0 := ball_subset_ball hrr0 hx
  have hball : closedBall x (r0 / 2) ⊆ ball p (2 * r0) := by
    intro z hz
    have hh := dist_triangle z x p
    have hz' : dist z x ≤ r0 / 2 := hz
    have hx' : dist x p < r0 := hx0
    rw [mem_ball]
    linarith
  have hforce (j : Fin N) : Integrable (fun z => |f j z| * ‖z - x‖ ^ (-s)) ∧
      (∫ z, |f j z| * ‖z - x‖ ^ (-s)) ≤ Fj j := by
    obtain ⟨hi, hbnd⟩ := forcing_weight_of_local_energy E (f j) hE hE0 (hf j)
      isOpen_ball.measurableSet hC hs hsa (show 0 < r0 / 2 by positivity)
      (by filter_upwards [hgrowth j] with z hz hzU; exact hz (hU0 hzU))
      x hball (henergy0 x hx0).1
    refine ⟨hi, hbnd.trans ?_⟩
    exact add_le_add (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (henergy0 x hx0).2) hC) le_rfl
  have hj (j : Fin N) :
      IntegrableOn (fun z => ‖z - x‖ ^ (-(s + 1)) * ∑ i : Fin 2, |d j i z|)
        (ball p (2 * r)) ∧
      (∫ z in ball p (2 * r), ‖z - x‖ ^ (-(s + 1)) * ∑ i : Fin 2, |d j i z|) ≤
        Aj j + Cj j * Fj j := by
    have hxj : x ∈ ball p (rj j) := ball_subset_ball (by linarith [hrrj j]) hx
    have hh := hgrad j x hxj
    rw [show 1 - (s + 1) = -s by ring] at hh
    obtain ⟨hi, hbnd⟩ := hh (hforce j).1
    have hsub := ball_subset_ball (α := LoopPlane) (x := p) (hrrj j)
    refine ⟨hi.mono_set hsub, ?_⟩
    refine (setIntegral_mono_set hi (ae_of_all _ fun z => by positivity)
      hsub.eventuallyLE).trans (hbnd.trans ?_)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hforce j).2 (hCj j).le)
  have hsum : (fun z => ‖z - x‖ ^ (-(s + 1)) *
      (∑ j : Fin N, ∑ i : Fin 2, |d j i z|)) =
        (fun z => ∑ j : Fin N, ‖z - x‖ ^ (-(s + 1)) * ∑ i : Fin 2, |d j i z|) := by
    funext z
    exact Finset.mul_sum _ _ _
  constructor
  · rw [hsum]
    exact integrable_finsetSum _ fun j _ => (hj j).1
  · rw [hsum]
    rw [integral_finsetSum _ fun j _ => (hj j).1]
    exact Finset.sum_le_sum fun j _ => (hj j).2

set_option maxHeartbeats 1800000 in




theorem energy_weight_increment {N : ℕ} (u : Fin N → ScalarL2 2)
    (d : Fin N → Fin 2 → ScalarL2 2) (f v : Fin N → LoopPlane → ℝ)
    (hf : ∀ j, Integrable (f j)) {U : Set LoopPlane} (hU : IsOpen U)
    {R : ℝ} (hfs : ∀ j, Function.support (f j) ⊆ closedBall (0 : LoopPlane) R)
    (hweak : ∀ j i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d j i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u j z * fderiv ℝ φ z (EuclideanSpace.single i 1)))
    (heq : ∀ j (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f j z * φ z))
    {C B V H α β : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V) (hH : 0 ≤ H)
    (hβ : 0 < β) (hβα : β / 2 < α) (hα1 : α ≤ 1)
    (hgrowth : ∀ j, ∀ᵐ z ∂volume, z ∈ U →
      |f j z| ≤ C * (∑ k : Fin N, ∑ i : Fin 2, (d k i z) ^ 2))
    (hbound : ∀ j, ∀ᵐ z ∂volume, ‖u j z‖ ≤ B)
    (hvalue : ∀ x ∈ U, ∀ j, |v j x| ≤ V)
    (hsmall : ∀ x ∈ U, ∀ᵐ z ∂volume, z ∈ U →
      |∑ j : Fin N, f j z * (u j z - v j x)| ≤
        (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) / 2)
    (hholder : ∀ x ∈ U, ∀ j, ∀ᵐ z ∂volume, z ∈ U →
      |u j z - v j x| ≤ H * ‖z - x‖ ^ β)
    {p : LoopPlane} (hp : p ∈ U)
    (henergy : WeightedIntegralNear (fun z => ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) p α) :
    WeightedIntegralNear (fun z => ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) p (α + β / 2) := by
  have hgrad := gradient_weight_of_energy u d f hf hU hfs hweak heq hC
    (s := α - β / 2) (by linarith) (by linarith) (by linarith) hgrowth hp henergy
  obtain ⟨R0, hR0, hR0U⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp)
  obtain ⟨r, hr, hrR, A, hA, hgrad0⟩ := hgrad.exists_radius
    (fun z => by positivity) (show 0 < R0 / 4 by positivity)
  have hsub : ball p (2 * r) ⊆ U := ball_subset_closedBall.trans
    ((closedBall_subset_closedBall (by linarith)).trans hR0U)
  obtain ⟨θ, _hθc, _hθs, hθ⟩ := M65Interior.exists_disk_cutoff isOpen_univ p
    (show 0 ≤ 2 * r by positivity) (subset_univ _)
  let cut : ContDiffBump p := {
    rIn := r
    rOut := 3 * r / 2
    rIn_pos := hr
    rIn_lt_rOut := by linarith }
  let χ : 𝓢(LoopPlane, ℝ) := cut.hasCompactSupport.toSchwartzMap cut.contDiff
  have hχsupport : tsupport χ ⊆ ball p (2 * r) := by
    change tsupport cut ⊆ ball p (2 * r)
    rw [cut.tsupport_eq]
    exact closedBall_subset_ball (by dsimp only [cut]; linarith)
  have hχbound (z : LoopPlane) : |χ z| ≤ 1 := by
    change |cut z| ≤ 1
    rw [abs_of_nonneg cut.nonneg]
    exact cut.le_one
  have hα : 0 ≤ α + β / 2 := by linarith
  have hpower : α + β / 2 + 1 - β = α - β / 2 + 1 := by ring
  obtain ⟨K, hK, hstep⟩ := centered_weighted_energy_step u d f hf isOpen_ball hweak
    (fun j φ hc hs => heq j φ hc (hs.trans hsub)) θ
    (fun z hz => ⟨(hθ z (ball_subset_closedBall hz)).2.1,
      (hθ z (ball_subset_closedBall hz)).2.2⟩)
    hV hH hα (show 0 < r / 2 by positivity) (by linarith : 1 < α + β / 2 + 1 - β)
    hbound χ cut.hasCompactSupport hχsupport hχbound
  refine ⟨r / 4, by positivity, K + 4 * (α + β / 2) * H * A, by positivity, ?_⟩
  intro x hx
  have hxr : x ∈ ball p r := ball_subset_ball (by linarith) hx
  have hxU : x ∈ U := hsub (ball_subset_ball (by linarith) hx)
  have hball : closedBall x (r / 2) ⊆ ball p (2 * r) := by
    intro z hz
    have hh := dist_triangle z x p
    have hz' : dist z x ≤ r / 2 := hz
    have hx' : dist x p < r / 4 := hx
    rw [mem_ball]
    linarith
  have hflat (z : LoopPlane) (hz : ‖z - x‖ < r / 2) (i : Fin 2) :
      fderiv ℝ χ z (EuclideanSpace.single i 1) = 0 := by
    have hzp : z ∈ ball p cut.rIn := by
      have hh := dist_triangle z x p
      have hx' : dist x p < r / 4 := hx
      have hz' : dist z x < r / 2 := by simpa only [dist_eq_norm] using hz
      change dist z p < r
      linarith
    have hone : χ =ᶠ[𝓝 z] fun _ => (1 : ℝ) := cut.eventuallyEq_one_of_mem_ball hzp
    rw [hone.fderiv_eq, fderiv_const_apply, zero_apply]
  have hJ : IntegrableOn (fun z => ‖z - x‖ ^ (-(α + β / 2 + 1 - β)) *
      (∑ j : Fin N, ∑ i : Fin 2, |d j i z|)) (ball p (2 * r)) := by
    simpa only [hpower] using (hgrad0 x hxr).1
  obtain ⟨hi, hbnd⟩ := hstep x (fun j => v j x) (hvalue x hxU) hball
    (by filter_upwards [hsmall x hxU] with z hz hzU; exact hz (hsub hzU))
    (fun j => by filter_upwards [hholder x hxU j] with z hz hzU; exact hz (hsub hzU)) hflat hJ
  have hone (z : LoopPlane) (hz : z ∈ ball p (2 * (r / 4))) : χ z = 1 := by
    apply cut.one_of_mem_closedBall
    have hh : dist z p < 2 * (r / 4) := hz
    change dist z p ≤ r
    linarith
  have heqLocal : (fun z => χ z ^ 2 * ‖z - x‖ ^ (-(α + β / 2)) *
      (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2)) =ᵐ[volume.restrict (ball p (2 * (r / 4)))]
        (fun z => ‖z - x‖ ^ (-(α + β / 2)) *
          (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2)) := by
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with z hz
    rw [hone z hz, one_pow, one_mul]
  refine ⟨hi.integrableOn.congr heqLocal, ?_⟩
  rw [← integral_congr_ae heqLocal]
  refine (setIntegral_le_integral hi (ae_of_all _ fun z => by positivity)).trans (hbnd.trans ?_)
  rw [hpower]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hgrad0 x hxr).2 (by positivity))




theorem energy_weight_above_one {N : ℕ} (u : Fin N → ScalarL2 2)
    (d : Fin N → Fin 2 → ScalarL2 2) (f v : Fin N → LoopPlane → ℝ)
    (hf : ∀ j, Integrable (f j)) {U : Set LoopPlane} (hU : IsOpen U)
    {R : ℝ} (hfs : ∀ j, Function.support (f j) ⊆ closedBall (0 : LoopPlane) R)
    (hweak : ∀ j i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d j i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u j z * fderiv ℝ φ z (EuclideanSpace.single i 1)))
    (heq : ∀ j (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f j z * φ z))
    {C B V H β : ℝ} (hC : 0 ≤ C) (hV : 0 ≤ V) (hH : 0 ≤ H) (hβ : 0 < β)
    (hgrowth : ∀ j, ∀ᵐ z ∂volume, z ∈ U →
      |f j z| ≤ C * (∑ k : Fin N, ∑ i : Fin 2, (d k i z) ^ 2))
    (hbound : ∀ j, ∀ᵐ z ∂volume, ‖u j z‖ ≤ B)
    (hvalue : ∀ x ∈ U, ∀ j, |v j x| ≤ V)
    (hsmall : ∀ x ∈ U, ∀ᵐ z ∂volume, z ∈ U →
      |∑ j : Fin N, f j z * (u j z - v j x)| ≤
        (∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) / 2)
    (hholder : ∀ x ∈ U, ∀ j, ∀ᵐ z ∂volume, z ∈ U →
      |u j z - v j x| ≤ H * ‖z - x‖ ^ β)
    {p : LoopPlane} (hp : p ∈ U)
    (henergy : WeightedIntegralNear (fun z => ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) p β) :
    ∃ a > 1, WeightedIntegralNear (fun z => ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) p a := by
  by_contra! hno
  have hseq (n : ℕ) : WeightedIntegralNear
      (fun z => ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) p (β + (n : ℝ) * (β / 2)) := by
    induction n with
    | zero => simpa only [Nat.cast_zero, zero_mul, add_zero] using henergy
    | succ n ih =>
      have hα1 : β + (n : ℝ) * (β / 2) ≤ 1 := le_of_not_gt (fun hh => hno _ hh ih)
      have hβα : β / 2 < β + (n : ℝ) * (β / 2) := by
        have hn : 0 ≤ (n : ℝ) * (β / 2) := mul_nonneg (Nat.cast_nonneg n) (by positivity)
        linarith
      have hnext := energy_weight_increment u d f v hf hU hfs hweak heq
        hC hV hH hβ hβα hα1 hgrowth hbound hvalue hsmall hholder hp ih
      convert hnext using 1
      push_cast
      ring
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / β)
  have hm : 2 < (n : ℝ) * β := (div_lt_iff₀ hβ).mp hn
  have hlarge : 1 < β + (n : ℝ) * (β / 2) := by nlinarith
  exact hno _ hlarge (hseq n)

set_option maxHeartbeats 900000 in





theorem C1_of_energy_weight {N : ℕ} (u : Fin N → ScalarL2 2)
    (d : Fin N → Fin 2 → ScalarL2 2) (f v : Fin N → LoopPlane → ℝ)
    (hf : ∀ j, Integrable (f j)) {U : Set LoopPlane} (hU : IsOpen U)
    {R : ℝ} (hfs : ∀ j, Function.support (f j) ⊆ closedBall (0 : LoopPlane) R)
    (hweak : ∀ j i (φ : 𝓢(LoopPlane, ℝ)),
      ⟪d j i, φ.toLp 2 volume⟫_ℝ =
        -(∫ z, u j z * fderiv ℝ φ z (EuclideanSpace.single i 1)))
    (heq : ∀ j (φ : 𝓢(LoopPlane, ℝ)), HasCompactSupport φ → tsupport φ ⊆ U →
      (∑ i : Fin 2, ⟪d j i, (∂_{EuclideanSpace.single i (1 : ℝ)} φ).toLp 2 volume⟫_ℝ) =
        -(∫ z, f j z * φ z))
    {C a : ℝ} (hC : 0 ≤ C) (ha : 1 < a)
    (hgrowth : ∀ j, ∀ᵐ z ∂volume, z ∈ U →
      |f j z| ≤ C * (∑ k : Fin N, ∑ i : Fin 2, (d k i z) ^ 2))
    (hv : ∀ j, ContinuousOn (v j) U)
    (huv : ∀ j, (u j : LoopPlane → ℝ) =ᵐ[volume.restrict U] v j)
    {p : LoopPlane} (hp : p ∈ U)
    (henergy : WeightedIntegralNear (fun z => ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2) p a) :
    ∃ r > 0, ball p r ⊆ U ∧ ∀ j, ContDiffOn ℝ 1 (v j) (ball p r) := by
  let E := fun z => ∑ j : Fin N, ∑ i : Fin 2, (d j i z) ^ 2
  have hE : Integrable E := integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun i _ => (Lp.memLp (d j i)).integrable_sq
  have hE0 (z : LoopPlane) : 0 ≤ E z := by dsimp only [E]; positivity
  obtain ⟨R0, hR0, hR0U⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp)
  obtain ⟨r, hr, hrR, B, hB, henergy0⟩ :=
    henergy.exists_radius hE0 (show 0 < R0 / 4 by positivity)
  have hsub : ball p (2 * r) ⊆ U := ball_subset_closedBall.trans
    ((closedBall_subset_closedBall (by linarith)).trans hR0U)
  have hrU : ball p r ⊆ U := (ball_subset_ball (by linarith)).trans hsub
  refine ⟨r, hr, hrU, ?_⟩
  intro j
  have hforce (x : LoopPlane) (hx : x ∈ ball p r) :
      Integrable (fun z => |f j z| * ‖x - z‖ ^ (-a)) ∧
      (∫ z, |f j z| * ‖x - z‖ ^ (-a)) ≤
        C * ((∫ z, E z) + B) + (r / 2) ^ (-a) * ∫ z, |f j z| := by
    have hball : closedBall x (r / 2) ⊆ ball p (2 * r) := by
      intro z hz
      have hh := dist_triangle z x p
      have hz' : dist z x ≤ r / 2 := hz
      have hx' : dist x p < r := hx
      rw [mem_ball]
      linarith
    obtain ⟨hi, hbnd⟩ := forcing_weight_of_local_energy E (f j) hE hE0 (hf j)
      isOpen_ball.measurableSet hC (lt_trans zero_lt_one ha) le_rfl
      (show 0 < r / 2 by positivity)
      (by filter_upwards [hgrowth j] with z hz hzU; exact hz (hsub hzU))
      x hball (henergy0 x hx).1
    rw [show (fun z => |f j z| * ‖x - z‖ ^ (-a)) =
      (fun z => |f j z| * ‖z - x‖ ^ (-a)) by funext z; rw [norm_sub_rev]]
    refine ⟨hi, hbnd.trans ?_⟩
    exact add_le_add (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (henergy0 x hx).2) hC) le_rfl
  exact plane_weak_C1_of_weight (u j) (d j) (f j) (hf j) isOpen_ball (hfs j)
    (hweak j) (fun φ hc hs => heq j φ hc (hs.trans hrU)) (v j) ((hv j).mono hrU)
    (ae_restrict_of_ae_restrict_of_subset hrU (huv j)) ha
    (fun x hx => (hforce x hx).1) (fun x hx => (hforce x hx).2)




theorem initial_energy_weight
    (E : LoopPlane → ℝ) (hE : Integrable E) (hE0 : ∀ z, 0 ≤ E z)
    (p : LoopPlane) {R β C : ℝ} (hR : 0 < R) (hβ : 0 < β) (hC : 0 ≤ C)
    (hdecay : ∀ x ∈ ball p R, ∀ r : ℝ, 0 < r → r ≤ R →
      (∫ z in closedBall x r, E z) ≤ C * r ^ (2 * β)) :
    WeightedIntegralNear E p β := by
  obtain ⟨K, hK, hweight⟩ := weighted_energy_of_disk_decay hR hβ
    (by linarith : β < 2 * β) hC
  refine ⟨R / 4, by positivity, K, hK, ?_⟩
  intro x hx
  have hxR : x ∈ ball p R := ball_subset_ball (by linarith) hx
  obtain ⟨hi, hb⟩ := hweight x E hE hE0 (hdecay x hxR)
  have hsub : ball p (2 * (R / 4)) ⊆ closedBall x R := by
    intro z hz
    have hh := dist_triangle z p x
    have hz' : dist z p < 2 * (R / 4) := hz
    have hx' : dist x p < R / 4 := hx
    rw [dist_comm p x] at hh
    rw [mem_closedBall]
    linarith
  exact ⟨hi.mono_set hsub, (setIntegral_mono_set hi
    (ae_of_all _ fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hE0 z))
      hsub.eventuallyLE).trans hb⟩

end PoincareConjecture.M65Boundary
