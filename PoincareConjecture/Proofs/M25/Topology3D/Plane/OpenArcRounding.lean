import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenArcLinearExtension
import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenArcRoundingProducer
import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenLineInjection
import PoincareConjecture.Proofs.M25.Topology3D.Plane.SmoothAbsolute











set_option autoImplicit false

open Set Function
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

variable {n : ℕ}



noncomputable def roundedOpenArcParameter (ρ : ℝ → ℝ)
    (p : Polygon (ℝ × ℝ) (n + 2)) : ℝ → ℝ × ℝ :=
  roundedVertexPath ρ (openArcExtendedVertex p)

private theorem openArcExtendedVertex_identity (p : Polygon (ℝ × ℝ) (n + 2))
    (hp : ∀ k, p k = ((k.val : ℝ), 0)) (j : ℤ) :
    openArcExtendedVertex p j = ((j : ℝ), 0) := by
  by_cases hj : 0 ≤ j ∧ j ≤ (n + 1 : ℕ)
  · let k : Fin (n + 2) := ⟨j.toNat, (Int.toNat_lt hj.1).mpr (by omega)⟩
    have hk : (k.val : ℤ) = j := Int.toNat_of_nonneg hj.1
    rw [← hk, openArcExtendedVertex_nat, hp]
    simp only [Int.cast_natCast]
  · exact if_neg hj



theorem roundedOpenArcParameter_identity (ρ : ℝ → ℝ)
    (p : Polygon (ℝ × ℝ) (n + 2))
    (hp : ∀ k, p k = ((k.val : ℝ), 0)) (u : ℝ) :
    roundedOpenArcParameter ρ p u = (u, 0) := by
  let j : ℤ := ⌊u + 1 / 2⌋
  change roundedCorner ρ (openArcExtendedVertex p j)
    (openArcExtendedVertex p j - openArcExtendedVertex p (j - 1))
    (openArcExtendedVertex p (j + 1) - openArcExtendedVertex p j) (u - j) = _
  rw [openArcExtendedVertex_identity p hp j, openArcExtendedVertex_identity p hp (j - 1),
    openArcExtendedVertex_identity p hp (j + 1), roundedCorner]
  simp only [Int.cast_sub, Int.cast_add, Int.cast_one]
  ext <;> dsimp <;> ring



theorem roundedOpenArcParameter_axis (ρ : ℝ → ℝ)
    (p : Polygon (ℝ × ℝ) (n + 2)) (hp : ∀ k, (p k).2 = 0) (u : ℝ) :
    (roundedOpenArcParameter ρ p u).2 = 0 := by
  have hP (j : ℤ) : (openArcExtendedVertex p j).2 = 0 := by
    by_cases hj : 0 ≤ j ∧ j ≤ (n + 1 : ℕ)
    · simpa only [openArcExtendedVertex, if_pos hj] using hp (polygonIntegerIndex (n + 2) j)
    · simp only [openArcExtendedVertex, if_neg hj]
  simp only [roundedOpenArcParameter, roundedVertexPath, roundedCorner,
    Prod.snd_add, Prod.smul_snd, Prod.snd_sub, hP, sub_self, smul_zero, add_zero]



theorem roundedOpenArcParameter_tail (ρ : ℝ → ℝ)
    (p : Polygon (ℝ × ℝ) (n + 2)) (u : ℝ) (hu : (n + 6 : ℕ) ≤ |u|) :
    roundedOpenArcParameter ρ p u = (u, 0) := by
  let j : ℤ := ⌊u + 1 / 2⌋
  have hlo : (j : ℝ) ≤ u + 1 / 2 := Int.floor_le _
  have hhi : u + 1 / 2 < (j : ℝ) + 1 := Int.lt_floor_add_one _
  have hcase : j + 1 < 0 ∨ (n + 1 : ℕ) < j - 1 := by
    by_cases hu0 : 0 ≤ u
    · right
      rw [abs_of_nonneg hu0] at hu
      have hj : ((n + 1 : ℕ) : ℝ) < (j : ℝ) - 1 := by
        push_cast at hu ⊢
        linarith
      exact_mod_cast hj
    · left
      rw [abs_of_neg (lt_of_not_ge hu0)] at hu
      have hj : (j : ℝ) + 1 < 0 := by
        push_cast at hu
        linarith [Nat.cast_nonneg (α := ℝ) n]
      exact_mod_cast hj
  have hP (k : ℤ) (hk : j - 1 ≤ k ∧ k ≤ j + 1) :
      openArcExtendedVertex p k = ((k : ℝ), 0) := by
    have hnot : ¬ (0 ≤ k ∧ k ≤ (n + 1 : ℕ)) := by
      rcases hcase with hcase | hcase <;> omega
    exact if_neg hnot
  change roundedCorner ρ (openArcExtendedVertex p j)
    (openArcExtendedVertex p j - openArcExtendedVertex p (j - 1))
    (openArcExtendedVertex p (j + 1) - openArcExtendedVertex p j) (u - j) = _
  rw [hP j (by omega), hP (j - 1) (by omega), hP (j + 1) (by omega), roundedCorner]
  simp only [Int.cast_sub, Int.cast_add, Int.cast_one]
  ext <;> dsimp <;> ring

private theorem dist_roundedVertexPath_abs_le (P : ℤ → ℝ × ℝ)
    {ρ : ℝ → ℝ} {δ B : ℝ} (hδ : 0 < δ)
    (hbound : ∀ u, |u| ≤ ρ u ∧ ρ u ≤ |u| + δ)
    (hB : ∀ j : ℤ, ‖(P (j + 1) - P j) - (P j - P (j - 1))‖ ≤ B) (t : ℝ) :
    dist (roundedVertexPath ρ P t) (roundedVertexPath abs P t) ≤ δ / 2 * B := by
  let j : ℤ := ⌊t + 1 / 2⌋
  let u : ℝ := t - j
  have heq : roundedCorner ρ (P j) (P j - P (j - 1)) (P (j + 1) - P j) u -
      roundedCorner abs (P j) (P j - P (j - 1)) (P (j + 1) - P j) u =
        ((ρ u - |u|) / 2) • ((P (j + 1) - P j) - (P j - P (j - 1))) := by
    dsimp only [roundedCorner]
    module
  have hnonneg : 0 ≤ (ρ u - |u|) / 2 := by linarith [(hbound u).1]
  have hle : (ρ u - |u|) / 2 ≤ δ / 2 := by linarith [(hbound u).2]
  change dist (roundedCorner ρ _ _ _ u) (roundedCorner abs _ _ _ u) ≤ _
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact mul_le_mul hle (hB j) (norm_nonneg _) (by linarith)





theorem exists_smooth_rounded_openArc_family
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (p : (ℝ × ℝ) → Polygon (ℝ × ℝ) (n + 2))
    (hp : ∀ k, ContDiff ℝ ∞ (fun z => p z k))
    (hgood : ∀ z ∈ K, IsSimplePolygonalArc (p z) ∧ p z 0 = (0, 0) ∧
      p z (Fin.last (n + 1)) = (((n + 1 : ℕ) : ℝ), 0) ∧
      ∀ k, k ≠ 0 → k ≠ Fin.last (n + 1) →
        0 < (p z k).1 ∧ (p z k).1 < (n + 1 : ℕ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ ∃ ρ : ℝ → ℝ,
      ContDiff ℝ ∞ ρ ∧ (∀ u, δ ≤ |u| → ρ u = |u|) ∧
      (∀ u, |u| ≤ ρ u ∧ ρ u ≤ |u| + δ) ∧ (∀ u, |deriv ρ u| ≤ 1) ∧
      ContDiff ℝ ∞ (fun x : (ℝ × ℝ) × ℝ => roundedOpenArcParameter ρ (p x.1) x.2) ∧
      (∀ z ∈ K, Injective (roundedOpenArcParameter ρ (p z))) ∧
      (∀ z ∈ K, ∀ u, fderiv ℝ (roundedOpenArcParameter ρ (p z)) u 1 ≠ 0) ∧
      (∀ z, ∀ u : ℝ, (n + 6 : ℕ) ≤ |u| → roundedOpenArcParameter ρ (p z) u = (u, 0)) ∧
      (∀ z ∈ K, ∀ u, dist (roundedOpenArcParameter ρ (p z) u)
        (openArcLinearParameter (p z) u) < ε) ∧
      (∀ z, (∀ k, p z k = ((k.val : ℝ), 0)) →
        ∀ u, roundedOpenArcParameter ρ (p z) u = (u, 0)) ∧
      ∀ z, (∀ k, (p z k).2 = 0) → ∀ u, (roundedOpenArcParameter ρ (p z) u).2 = 0 := by
  let P : (ℝ × ℝ) → ℤ → ℝ × ℝ := fun z => openArcExtendedVertex (p z)
  let Q : (ℝ × ℝ) → ℤ → ℝ × ℝ := fun z j =>
    (P z (j + 1) - P z j) - (P z j - P z (j - 1))
  have hP (j : ℤ) : ContDiff ℝ ∞ (fun z => P z j) := contDiff_openArcExtendedVertex hp j
  have hQ (j : ℤ) : Continuous (fun z => Q z j) :=
    (((hP (j + 1)).sub (hP j)).sub ((hP j).sub (hP (j - 1)))).continuous
  have hsum : Continuous (fun z => ∑ k : Fin (n + 2), ‖Q z (k.val : ℤ)‖) :=
    continuous_finsetSum _ (fun k _ => (hQ (k.val : ℤ)).norm)
  obtain ⟨b, hb⟩ := hK.bddAbove_image hsum.continuousOn
  let B : ℝ := max b 0 + 1
  have hBpos : 0 < B := by dsimp only [B]; positivity
  have hB (z : ℝ × ℝ) (hz : z ∈ K) (j : ℤ) : ‖Q z j‖ ≤ B := by
    by_cases hj : 0 ≤ j ∧ j ≤ (n + 1 : ℕ)
    · let k : Fin (n + 2) := ⟨j.toNat, (Int.toNat_lt hj.1).mpr (by omega)⟩
      have hk : (k.val : ℤ) = j := Int.toNat_of_nonneg hj.1
      calc
        ‖Q z j‖ = ‖Q z (k.val : ℤ)‖ := by rw [hk]
        _ ≤ ∑ l : Fin (n + 2), ‖Q z (l.val : ℤ)‖ :=
          Finset.single_le_sum (fun l _ => norm_nonneg (Q z (l.val : ℤ))) (Finset.mem_univ k)
        _ ≤ b := hb ⟨z, hz, rfl⟩
        _ ≤ B := by dsimp only [B]; linarith [le_max_left b 0]
    · have hzero : Q z j = 0 := openArcExtendedVertex_secondDiff_zero (p z)
        (hgood z hz).2.1 (hgood z hz).2.2.1 (by omega)
      rw [hzero, norm_zero]
      exact hBpos.le
  have hLinj (z : ℝ × ℝ) (hz : z ∈ K) : Injective (openArcLinearParameter (p z)) := by
    obtain ⟨hsimple, h0, hN, hstrip⟩ := hgood z hz
    apply openArcLinearParameter_injective (p z) hsimple h0 hN
    intro k
    by_cases hk0 : k = 0
    · rw [hk0, h0]
      exact ⟨le_rfl, by positivity⟩
    · by_cases hkN : k = Fin.last (n + 1)
      · rw [hkN, hN]
        exact ⟨by positivity, le_rfl⟩
      · exact ⟨(hstrip k hk0 hkN).1.le, (hstrip k hk0 hkN).2.le⟩
  have hLtail (z : ℝ × ℝ) (hz : z ∈ K) (u : ℝ) (hu : (n + 2 : ℕ) ≤ |u|) :
      openArcLinearParameter (p z) u = (u, 0) := by
    by_cases hu0 : u ≤ 0
    · exact openArcLinearParameter_of_nonpos (p z) (hgood z hz).2.1 hu0
    · apply openArcLinearParameter_of_ge (p z) (hgood z hz).2.2.1
      rw [abs_of_nonneg (le_of_not_ge hu0)] at hu
      push_cast at hu ⊢
      linarith
  obtain ⟨η, hη, hstable⟩ := exists_fixedTail_openLine_injection_tolerance hK
    (R := ((n + 2 : ℕ) : ℝ)) (r := 1 / 4) (by positivity) (by norm_num)
    (fun z => openArcLinearParameter (p z))
    (continuous_openArcLinearParameter (fun k => (hp k).continuous)).continuousOn hLinj hLtail
  obtain ⟨δ, hδ, hd⟩ := exists_between
    (show 0 < min (1 / 4 : ℝ) (min ε η / (2 * B)) by positivity)
  have hδquarter : δ < 1 / 4 := hd.trans_le (min_le_left _ _)
  have herr : 2 * δ * B < min ε η := by
    have h := (lt_div_iff₀ (show 0 < 2 * B by positivity)).mp
      (hd.trans_le (min_le_right _ _))
    nlinarith
  obtain ⟨ρ, hρ, _, _, htail, hbound, hder⟩ := exists_smooth_absolute_rounding hδ
  let data (z : ℝ × ℝ) (hz : z ∈ K) : OpenArcRoundedData ρ (fun _ => P z) :=
    { δ := δ
      delta_pos := hδ
      delta_quarter := hδquarter
      profile_tail := htail
      profile_bound := hbound
      profile_smooth := hρ
      profile_derivative := hder
      vertices_smooth := fun _ => contDiff_const
      corner_functional := fun _ j =>
        exists_positive_corner_functional_of_injective_vertexPath (P z) (hLinj z hz) j
      tail_radius := ((n + 2 : ℕ) : ℝ)
      tail_radius_pos := by positivity
      vertex_tail := by
        intro _ j hj
        have hnot : ¬ (0 ≤ j ∧ j ≤ (n + 1 : ℕ)) := by
          rintro ⟨hj0, hjN⟩
          have hj0' : 0 ≤ (j : ℝ) := by exact_mod_cast hj0
          have hjN' : (j : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hjN
          rw [abs_of_nonneg hj0'] at hj
          push_cast at hj hjN'
          linarith
        exact if_neg hnot }
  have hclose (z : ℝ × ℝ) (hz : z ∈ K) (u : ℝ) :
      dist (roundedOpenArcParameter ρ (p z) u) (openArcLinearParameter (p z) u) < min ε η := by
    calc
      dist (roundedOpenArcParameter ρ (p z) u) (openArcLinearParameter (p z) u) ≤ δ / 2 * B :=
        dist_roundedVertexPath_abs_le (P z) hδ hbound (hB z hz) u
      _ ≤ 2 * δ * B := by nlinarith
      _ < min ε η := herr
  have hlocal (z : ℝ × ℝ) (hz : z ∈ K) : ∀ s t : ℝ, |s - t| < 1 / 4 →
      roundedOpenArcParameter ρ (p z) s = roundedOpenArcParameter ρ (p z) t → s = t := by
    simpa only [roundedOpenArcParameter, openArcRoundedFamily, P] using
      openArcRoundedFamily_local_injective (data z hz) 0
  refine ⟨δ, hδ, hδquarter, ρ, hρ, htail, hbound, hder, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_roundedVertexPath hδ (by linarith) htail hbound hρ hP
  · exact hstable (fun z => roundedOpenArcParameter ρ (p z))
      (fun z hz u => (hclose z hz u).trans_le (min_le_right _ _)) hlocal
  · intro z hz u
    have hreg := openArcRoundedFamily_fderiv_regular (data z hz) 0 u
    exact hreg
  · exact fun z u hu => roundedOpenArcParameter_tail ρ (p z) u hu
  · intro z hz u
    exact (hclose z hz u).trans_le (min_le_left _ _)
  · exact fun z hmesh u => roundedOpenArcParameter_identity ρ (p z) hmesh u
  · exact fun z haxis u => roundedOpenArcParameter_axis ρ (p z) haxis u

end PoincareConjecture.M25.Topology3D
