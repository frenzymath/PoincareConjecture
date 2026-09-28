import PoincareConjecture.Proofs.M25.Topology3D.Plane.RoundedVertexPath
import PoincareConjecture.Proofs.M25.Topology3D.Plane.ChordEstimates

set_option autoImplicit false

open Set Metric Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_roundedVertexPath_local {ρ : ℝ → ℝ} (P : ℤ → E) {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) (i : ℤ) {t : ℝ}
    (ht : t ∈ Ioo ((i : ℝ) - 1 + δ) ((i : ℝ) + 1 - δ))
    (hρ : DifferentiableAt ℝ ρ (t - i)) :
    HasDerivAt (roundedVertexPath ρ P)
      (((1 - deriv ρ (t - i)) / 2) • (P i - P (i - 1)) +
        ((1 + deriv ρ (t - i)) / 2) • (P (i + 1) - P i)) t := by
  have h := (hasDerivAt_roundedCorner (P i) (P i - P (i - 1))
    (P (i + 1) - P i) hρ).scomp t ((hasDerivAt_id t).sub_const (i : ℝ))
  simp only [Function.comp_def, id_eq, one_smul] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact roundedVertexPath_eq_local P hδ hδhalf htail hbound i hs

theorem dist_roundedCorner_le_of_vertex_dist_le {ρ : ℝ → ℝ}
    (p u v y : E) {ε δ t : ℝ} (_hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (ht : |t| ≤ 1 / 2) (hρ : |t| ≤ ρ t ∧ ρ t ≤ |t| + δ)
    (hp : dist p y ≤ ε) (hu : dist (p - u) y ≤ ε) (hv : dist (p + v) y ≤ ε) :
    dist (roundedCorner ρ p u v t) y ≤ ε := by
  let a := (ρ t - t) / 2
  let b := (ρ t + t) / 2
  let k := 1 - ρ t
  have ha : 0 ≤ a := by dsimp [a]; linarith [le_abs_self t, hρ.1]
  have hb : 0 ≤ b := by dsimp [b]; linarith [neg_le_abs t, hρ.1]
  have hk : 0 ≤ k := by dsimp [k]; linarith [hρ.2]
  have heq : roundedCorner ρ p u v t - y =
      k • (p - y) + a • (p - u - y) + b • (p + v - y) := by
    dsimp [roundedCorner, k, a, b]
    module
  rw [dist_eq_norm] at hp hu hv ⊢
  rw [heq]
  calc
    ‖k • (p - y) + a • (p - u - y) + b • (p + v - y)‖ ≤
        ‖k • (p - y)‖ + ‖a • (p - u - y)‖ + ‖b • (p + v - y)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = k * ‖p - y‖ + a * ‖p - u - y‖ + b * ‖p + v - y‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ k * ε + a * ε + b * ε :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hp hk)
        (mul_le_mul_of_nonneg_left hu ha)) (mul_le_mul_of_nonneg_left hv hb)
    _ = ε := by dsimp [k, a, b]; ring

theorem exists_uniform_rounded_sampling_estimates {X : Type*} [PseudoMetricSpace X]
    {K : Set X} (hK : IsCompact K) {c d : X → ℝ → E} {l u : ℝ}
    (hc : ContinuousOn (fun p : X × ℝ => c p.1 p.2) (K ×ˢ Icc (l - 1) (u + 1)))
    (hd : ∀ z ∈ K, ∀ s ∈ Icc (l - 1) (u + 1), HasDerivAt (c z) (d z s) s)
    (hcont : ContinuousOn (fun p : X × ℝ => d p.1 p.2) (K ×ˢ Icc (l - 1) (u + 1)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧
      ∀ h : ℝ, 0 < h → h < η → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        ∀ ρ : ℝ → ℝ, Differentiable ℝ ρ →
          (∀ s, δ ≤ |s| → ρ s = |s|) →
          (∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) →
          (∀ s, |deriv ρ s| ≤ 1) → ∀ z ∈ K, ∀ t ∈ Icc l u,
            dist (roundedVertexPath ρ (fun i : ℤ => c z (h * i)) (t / h)) (c z t) < ε ∧
              ‖deriv (fun s => roundedVertexPath ρ (fun i : ℤ => c z (h * i)) (s / h)) t -
                d z t‖ < ε := by
  obtain ⟨rc, hrc, hclosec⟩ := Metric.uniformContinuousOn_iff.mp
    ((hK.prod isCompact_Icc).uniformContinuousOn_of_continuous hc) (ε / 2) (half_pos hε)
  obtain ⟨rd, hrd, hclosed⟩ := Metric.uniformContinuousOn_iff.mp
    ((hK.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont) (ε / 2) (half_pos hε)
  have hmin : 0 < min (1 / 2 : ℝ) (min rc rd / 2) := by positivity
  obtain ⟨η, hη, hηb⟩ := exists_between hmin
  have hηhalf : η < 1 / 2 := hηb.trans_le (min_le_left _ _)
  refine ⟨η, hη, hηhalf, ?_⟩
  intro h hh hηh δ hδ hδhalf ρ hρ htail hbound hder z hz t ht
  have hhh : h < 1 / 2 := hηh.trans hηhalf
  have hrc' : 2 * h < rc := by
    have h := hηb.trans_le (min_le_right _ _)
    linarith [min_le_left rc rd]
  have hrd' : 2 * h < rd := by
    have h := hηb.trans_le (min_le_right _ _)
    linarith [min_le_right rc rd]
  let j : ℤ := ⌊t / h + 1 / 2⌋
  let A : ℝ := h * j
  let P : ℤ → E := fun i => c z (h * i)
  have hjlo : (j : ℝ) ≤ t / h + 1 / 2 := Int.floor_le _
  have hjhi : t / h + 1 / 2 < (j : ℝ) + 1 := Int.lt_floor_add_one _
  have hAlo : t - h / 2 < A := by
    have h := (div_lt_iff₀ hh).mp (show t / h < (j : ℝ) + 1 / 2 by linarith)
    dsimp [A]
    nlinarith
  have hAhi : A ≤ t + h / 2 := by
    have h := (le_div_iff₀ hh).mp (show (j : ℝ) - 1 / 2 ≤ t / h by linarith)
    dsimp [A]
    nlinarith
  have htwide : t ∈ Icc (l - 1) (u + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hnear (s : ℝ) (hs : s ∈ Icc (A - h) (A + h)) : |s - t| < 2 * h := by
    rw [abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  have hwide (s : ℝ) (hs : s ∈ Icc (A - h) (A + h)) : s ∈ Icc (l - 1) (u + 1) := by
    rcases abs_lt.mp (hnear s hs) with ⟨hlo, hhi⟩
    constructor <;> linarith [ht.1, ht.2]
  have hpos (s : ℝ) (hs : s ∈ Icc (A - h) (A + h)) : dist (c z s) (c z t) ≤ ε / 2 := by
    apply le_of_lt
    apply hclosec (z, s) ⟨hz, hwide s hs⟩ (z, t) ⟨hz, htwide⟩
    simpa only [dist_prod_same_left, Real.dist_eq] using (hnear s hs).trans hrc'
  have hvel (s : ℝ) (hs : s ∈ Icc (A - h) (A + h)) : ‖d z s - d z t‖ ≤ ε / 2 := by
    have h := hclosed (z, s) ⟨hz, hwide s hs⟩ (z, t) ⟨hz, htwide⟩ (by
      simpa only [dist_prod_same_left, Real.dist_eq] using (hnear s hs).trans hrd')
    exact le_of_lt (by simpa only [dist_eq_norm] using h)
  have hprev : h * ((j - 1 : ℤ) : ℝ) = A - h := by
    simp only [Int.cast_sub, Int.cast_one]
    dsimp [A]
    ring
  have hnext : h * ((j + 1 : ℤ) : ℝ) = A + h := by
    simp only [Int.cast_add, Int.cast_one]
    dsimp [A]
    ring
  have hm : A ∈ Icc (A - h) (A + h) := ⟨by linarith, by linarith⟩
  have hl : A - h ∈ Icc (A - h) (A + h) := ⟨le_rfl, by linarith⟩
  have hr : A + h ∈ Icc (A - h) (A + h) := ⟨by linarith, le_rfl⟩
  constructor
  · change dist (roundedCorner ρ (P j) (P j - P (j - 1)) (P (j + 1) - P j)
      (t / h - j)) (c z t) < ε
    apply lt_of_le_of_lt (dist_roundedCorner_le_of_vertex_dist_le _ _ _ _ hδ hδhalf
      (by rw [abs_le]; constructor <;> linarith) (hbound (t / h - j)) ?_ ?_ ?_)
      (half_lt_self hε)
    · exact hpos A hm
    · simpa only [sub_sub_cancel, P, hprev] using hpos (A - h) hl
    · simpa only [add_sub_cancel, P, hnext] using hpos (A + h) hr
  · have hleft : ∀ s ∈ Icc (A - h) A, s ∈ Icc (A - h) (A + h) :=
      fun s hs => ⟨hs.1, hs.2.trans (by linarith)⟩
    have hright : ∀ s ∈ Icc A (A + h), s ∈ Icc (A - h) (A + h) :=
      fun s hs => ⟨(show A - h ≤ A by linarith).trans hs.1, hs.2⟩
    have hu := norm_slope_sub_le_of_deriv_sub_le (show A - h < A by linarith)
      (fun s hs => (hd z hz s (hwide s (hleft s hs))).hasDerivWithinAt)
      (fun s hs => hvel s (hleft s hs))
    have hv := norm_slope_sub_le_of_deriv_sub_le (show A < A + h by linarith)
      (fun s hs => (hd z hz s (hwide s (hright s hs))).hasDerivWithinAt)
      (fun s hs => hvel s (hright s hs))
    rw [slope_def_module, show A - (A - h) = h by ring] at hu
    rw [slope_def_module, show A + h - A = h by ring] at hv
    let U := h⁻¹ • (P j - P (j - 1))
    let V := h⁻¹ • (P (j + 1) - P j)
    have hU : ‖U - d z t‖ ≤ ε / 2 := by simpa only [U, P, hprev] using hu
    have hV : ‖V - d z t‖ ≤ ε / 2 := by simpa only [V, P, hnext] using hv
    let α := (1 - deriv ρ (t / h - j)) / 2
    let β := (1 + deriv ρ (t / h - j)) / 2
    have ha : 0 ≤ α := by dsimp [α]; linarith [(abs_le.mp (hder (t / h - j))).2]
    have hb : 0 ≤ β := by dsimp [β]; linarith [(abs_le.mp (hder (t / h - j))).1]
    have hlocal : t / h ∈ Ioo ((j : ℝ) - 1 + δ) ((j : ℝ) + 1 - δ) := by
      constructor <;> linarith
    have hactual := (hasDerivAt_roundedVertexPath_local P hδ hδhalf htail hbound
      j hlocal (hρ _)).scomp t ((hasDerivAt_id t).div_const h)
    simp only [Function.comp_def, id_eq, one_div] at hactual
    have heq : deriv (fun s => roundedVertexPath ρ P (s / h)) t = α • U + β • V := by
      rw [hactual.deriv]
      dsimp [α, β, U, V]
      simp only [smul_add, smul_smul]
      congr 1 <;> congr 1 <;> ring
    change ‖deriv (fun s => roundedVertexPath ρ P (s / h)) t - d z t‖ < ε
    rw [heq]
    have hsub : α • U + β • V - d z t = α • (U - d z t) + β • (V - d z t) := by
      dsimp [α, β]
      module
    rw [hsub]
    calc
      ‖α • (U - d z t) + β • (V - d z t)‖ ≤ ‖α • (U - d z t)‖ + ‖β • (V - d z t)‖ :=
        norm_add_le _ _
      _ = α * ‖U - d z t‖ + β * ‖V - d z t‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ α * (ε / 2) + β * (ε / 2) := add_le_add
        (mul_le_mul_of_nonneg_left hU ha) (mul_le_mul_of_nonneg_left hV hb)
      _ = ε / 2 := by dsimp [α, β]; ring
      _ < ε := half_lt_self hε

end PoincareConjecture.M25.Topology3D
