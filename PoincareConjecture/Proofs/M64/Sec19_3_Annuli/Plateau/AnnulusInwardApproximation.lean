import PoincareConjecture.Proofs.M64.Mathlib.InwardSmoothApproximation
import PoincareConjecture.Proofs.M64.Mathlib.RestrictedPullbackLp
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialGeometry

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace PoincareConjecture

local notation "S" => interior m64AnnulusDomain
local notation "I" => Icc (0 : ℝ) curvePeriod

private theorem shifted_halfDisk_mem {x H t : ℝ}
    (hx : H < x) (hP : x + H < curvePeriod) (ht : H + t < 1)
    {z : LoopPlane} (hz : z ∈ closedBall 0 H)
    (hz1 : 0 < z 1 + t) : z + annulusPoint x t ∈ S := by
  have hb (i : Fin 2) : |z i| ≤ H :=
    (PiLp.norm_apply_le z i).trans (mem_closedBall_zero_iff.mp hz)
  obtain ⟨h0l, h0r⟩ := abs_le.mp (hb 0)
  obtain ⟨_, h1r⟩ := abs_le.mp (hb 1)
  apply (m64AnnulusInterior_coordinates _).mpr
  change 0 < z 0 + x ∧ z 0 + x < curvePeriod ∧ 0 < z 1 + t ∧ z 1 + t < 1
  exact ⟨by linarith, by linarith, hz1, by linarith⟩

theorem m64Annulus_halfDisk_ae_mem {x H : ℝ}
    (hx : H < x) (hP : x + H < curvePeriod) (hH : H < 1) :
    ∀ᵐ z ∂volume.restrict (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}),
      z + annulusPoint x 0 ∈ S := by
  have hK : MeasurableSet (closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}) :=
    measurableSet_closedBall.inter
      (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous).measurableSet
  have hnull : ∀ᵐ z : LoopPlane ∂volume, z 1 ≠ 0 := by
    apply ae_iff.mpr
    simpa only [not_not] using m64_radial_line_null 0
  filter_upwards [ae_restrict_mem hK, ae_restrict_of_ae hnull] with z hz hn
  exact shifted_halfDisk_mem hx hP (by simpa using hH) hz.1
    (by simpa using lt_of_le_of_ne hz.2 (Ne.symm hn))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem m64Annulus_inward_strong_approximation
    {u : LoopPlane → E} {b : ℝ → E}
    (hs : ContDiffOn ℝ 1 u S) (hu : MemLp u 2 (volume.restrict S))
    (hD : ∀ i : Fin 2, MemLp (fun z => fderiv ℝ u z (EuclideanSpace.single i 1))
      2 (volume.restrict S))
    (hb : ∀ t ∈ Ioo (0 : ℝ) 1, MemLp (fun y => u (annulusPoint y t) - b y)
      2 (volume.restrict I))
    (htrace : Tendsto (fun t => eLpNorm (fun y => u (annulusPoint y t) - b y)
      2 (volume.restrict I)) (𝓝[>] (0 : ℝ)) (𝓝 0))
    {x H : ℝ} (hH0 : 0 < H) (hx : H < x)
    (hP : x + H < curvePeriod) (hH : H < 1) :
    let K := closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}
    ∃ f : ℕ → LoopPlane → E, (∀ j, ContDiff ℝ 1 (f j)) ∧
      Tendsto (fun j => eLpNorm (fun z => f j z - u (z + annulusPoint x 0))
        2 (volume.restrict K)) atTop (𝓝 0) ∧
      (∀ i : Fin 2, Tendsto (fun j => eLpNorm (fun z =>
        fderiv ℝ (f j) z (EuclideanSpace.single i 1) -
          fderiv ℝ u (z + annulusPoint x 0) (EuclideanSpace.single i 1))
            2 (volume.restrict K)) atTop (𝓝 0)) ∧
      Tendsto (fun j => eLpNorm (fun s => f j (annulusPoint s 0) - b (s + x))
        2 (volume.restrict (Icc (-H) H))) atTop (𝓝 0) := by
  let K := closedBall (0 : LoopPlane) H ∩ {z | 0 ≤ z 1}
  have hK : IsClosed K := isClosed_closedBall.inter
    (isClosed_le continuous_const (EuclideanSpace.proj 1).continuous)
  let t (j : ℕ) := ((1 - H) / 2) * (1 / 2 : ℝ) ^ j
  have ht0 (j : ℕ) : 0 < t j := mul_pos (by linarith) (pow_pos (by norm_num) _)
  have htb (j : ℕ) : t j ≤ (1 - H) / 2 :=
    mul_le_of_le_one_right (by linarith)
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  have htI (j : ℕ) : t j ∈ Ioo (0 : ℝ) 1 := ⟨ht0 j, by linarith [htb j]⟩
  have ht : Tendsto t atTop (𝓝 0) := by
    simpa only [t, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul ((1 - H) / 2)
  have htg : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall ht0⟩
  have hc : Continuous (fun s : ℝ => annulusPoint x s) := by
    have hd : ContDiff ℝ 1 (fun s : ℝ => annulusPoint x s) := by
      apply contDiff_euclidean.mpr
      intro i
      fin_cases i
      · exact contDiff_const
      · exact contDiff_id
    exact hd.continuous
  have hshift (j : ℕ) : MapsTo (fun z => z + annulusPoint x (t j)) K S := by
    intro z hz
    exact shifted_halfDisk_mem hx hP (by linarith [htb j]) hz.1
      (add_pos_of_nonneg_of_pos hz.2 (ht0 j))
  obtain ⟨f, hf, hmatch, hval, hcol⟩ := m64_exists_contDiff_inward_approximation
    isOpen_interior hK hs hu hD ((hc.tendsto 0).comp ht)
      (m64Annulus_halfDisk_ae_mem hx hP hH) hshift
  refine ⟨f, hf, hval, hcol, ?_⟩
  have hlim := htrace.comp htg
  have hbound (j : ℕ) :
      eLpNorm (fun s => f j (annulusPoint s 0) - b (s + x))
        2 (volume.restrict (Icc (-H) H)) ≤
      eLpNorm (fun y => u (annulusPoint y (t j)) - b y) 2 (volume.restrict I) := by
    have hmem : ∀ᵐ s ∂volume.restrict (Icc (-H) H), s + x ∈ I := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hpull := (m64MeasurePreserving_memLp_restrict
      (measurePreserving_add_right volume x) measurableSet_Icc hmem (hb (t j) (htI j))).2
    calc
      _ = eLpNorm (fun s => u (annulusPoint (s + x) (t j)) - b (s + x))
          2 (volume.restrict (Icc (-H) H)) := by
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
        have hnorm : ‖annulusPoint s 0‖ = |s| := by
          have heq : annulusPoint s 0 = EuclideanSpace.single (0 : Fin 2) s := by
            ext i
            fin_cases i <;> simp [annulusPoint]
          rw [heq, PiLp.norm_single, Real.norm_eq_abs]
        have hpoint : annulusPoint s 0 ∈ K :=
          ⟨mem_closedBall_zero_iff.mpr (by rw [hnorm]; exact abs_le.mpr hs),
            by simp [annulusPoint]⟩
        rw [(hmatch j _ hpoint).self_of_nhds]
        have heq : annulusPoint s 0 + annulusPoint x (t j) =
            annulusPoint (s + x) (t j) := by
          ext i
          fin_cases i <;> simp [annulusPoint]
        change u (annulusPoint s 0 + annulusPoint x (t j)) - b (s + x) = _
        rw [heq]
      _ ≤ _ := hpull
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hbound

end PoincareConjecture
