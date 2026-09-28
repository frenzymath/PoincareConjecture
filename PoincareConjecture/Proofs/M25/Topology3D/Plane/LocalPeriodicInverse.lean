import PoincareConjecture.Proofs.M25.Topology3D.Plane.PeriodicFiber
import PoincareConjecture.Proofs.M25.Topology3D.Plane.SupportedRadialSlide
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TimeCutoff

set_option autoImplicit false

open Set Function
open scoped Topology ContDiff

namespace PoincareConjecture.M25.Topology3D

theorem exists_smooth_local_inverse_of_add_period
    {L U a b T : ℝ} (ha : L < a) (hb : b < U) (hT : 0 < T)
    {F : ℝ × ℝ → ℝ} (hF : ContDiffOn ℝ ∞ F (Ioo L U ×ˢ univ))
    (hper : ∀ z ∈ Ioo L U, ∀ t, F (z, t + T) = F (z, t) + T)
    (hpos : ∀ z ∈ Ioo L U, ∀ t, 0 < deriv (fun s => F (z, s)) t) :
    ∃ G : ℝ × ℝ → ℝ, ContDiff ℝ ∞ G ∧
      (∀ z t, G (z, t + T) = G (z, t) + T) ∧
      ∀ z ∈ Icc a b, ∀ t, F (z, G (z, t)) = t ∧ G (z, F (z, t)) = t := by
  let ε := min (a - L) (U - b) / 2
  have hε : 0 < ε := div_pos (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb)) (by norm_num)
  let l := a - ε
  let u := b + ε
  have hl : L < l := by
    dsimp [l, ε]
    linarith [min_le_left (a - L) (U - b)]
  have hu : u < U := by
    dsimp [u, ε]
    linarith [min_le_right (a - L) (U - b)]
  have hKJ : Icc l u ⊆ Ioo L U := fun z hz =>
    ⟨hl.trans_le hz.1, hz.2.trans_lt hu⟩
  obtain ⟨τ, hτ, hτrange, hτone, hτtail⟩ := exists_smooth_interval_cutoff a b hε
  have hτzero (z : ℝ) (hz : z ∉ Icc l u) : τ z = 0 := by
    apply hτtail
    by_cases hlz : l ≤ z
    · exact Or.inr (lt_of_not_ge (fun h => hz ⟨hlz, h⟩)).le
    · exact Or.inl (lt_of_not_ge hlz).le
  let H : ℝ × ℝ → ℝ := fun p => p.2 + τ p.1 * (F p - p.2)
  have hH : ContDiff ℝ ∞ H := by
    exact contDiff_snd.add (contDiff_timeCutoff isClosed_Icc isOpen_Ioo hKJ hτ hτzero
      (hF.sub contDiff_snd.contDiffOn))
  have hHid (z : ℝ) (hz : z ∉ Ioo L U) : (fun t => H (z, t)) = id := by
    funext t
    simp only [H, hτzero z (fun h => hz (hKJ h)), zero_mul, add_zero, id_eq]
  have hHper (z t : ℝ) : H (z, t + T) = H (z, t) + T := by
    by_cases hz : z ∈ Ioo L U
    · dsimp only [H]
      rw [hper z hz]
      ring
    · exact congrFun (hHid z hz) (t + T) |>.trans
        (congrArg (fun x => x + T) (congrFun (hHid z hz) t)).symm
  have hHpos (z t : ℝ) : 0 < deriv (fun s => H (z, s)) t := by
    by_cases hz : z ∈ Ioo L U
    · have hFt : ContDiffAt ℝ ∞ (fun s => F (z, s)) t :=
        (hF.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hz, mem_univ t⟩)).comp t
          (contDiffAt_const.prodMk contDiffAt_id)
      have hder : HasDerivAt (fun s => H (z, s))
          (1 + τ z * (deriv (fun s => F (z, s)) t - 1)) t := by
        convert! (hasDerivAt_id t).add
          (((hFt.differentiableAt (by simp)).hasDerivAt.sub (hasDerivAt_id t)).const_mul (τ z))
          using 1
      rw [hder.deriv]
      by_cases hτ0 : τ z = 0
      · simp only [hτ0, zero_mul, add_zero, zero_lt_one]
      · have hτpos : 0 < τ z := lt_of_le_of_ne (hτrange z).1 (Ne.symm hτ0)
        nlinarith [mul_pos hτpos (hpos z hz t), (hτrange z).2]
    · rw [hHid z hz]
      simp only [deriv_id, zero_lt_one]
  obtain ⟨G, hG, hGinv⟩ := exists_smooth_inverse_of_add_period hT hH hHper hHpos
  refine ⟨G, hG, fun z t => (hGinv z t).2.2, ?_⟩
  intro z hz t
  have heq (s : ℝ) : H (z, s) = F (z, s) := by
    dsimp only [H]
    rw [hτone z hz]
    ring
  have hleft := (hGinv z t).1
  have hright := (hGinv z t).2.1
  rw [heq] at hleft hright
  exact ⟨hleft, hright⟩

end PoincareConjecture.M25.Topology3D
