import PoincareConjecture.Proofs.M25.Topology3D.Plane.RoundedVertexPath

set_option autoImplicit false

open Set Function Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

variable {ρ : ℝ → ℝ}
  {P : (ℝ × ℝ) → ℤ → (ℝ × ℝ)}

structure OpenArcRoundedData
    (ρ : ℝ → ℝ)
    (P : (ℝ × ℝ) → ℤ → (ℝ × ℝ)) : Type where
  δ : ℝ
  delta_pos : 0 < δ
  delta_quarter : δ < 1 / 4
  profile_tail : ∀ s, δ ≤ |s| → ρ s = |s|
  profile_bound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ
  profile_smooth : ContDiff ℝ ∞ ρ
  profile_derivative : ∀ s, |deriv ρ s| ≤ 1
  vertices_smooth : ∀ i, ContDiff ℝ ∞ (fun z : ℝ × ℝ => P z i)
  corner_functional : ∀ z i, ∃ ℓ : (ℝ × ℝ) →L[ℝ] ℝ,
    0 < ℓ (P z i - P z (i - 1)) ∧
      0 < ℓ (P z (i + 1) - P z i)
  tail_radius : ℝ
  tail_radius_pos : 0 < tail_radius
  vertex_tail : ∀ (z : ℝ × ℝ) (i : ℤ), tail_radius + 2 ≤ |(i : ℝ)| →
    P z i = ((i : ℝ), 0)

noncomputable def openArcRoundedFamily
    (ρ : ℝ → ℝ) (P : (ℝ × ℝ) → ℤ → (ℝ × ℝ))
    (z : ℝ × ℝ) (u : ℝ) : ℝ × ℝ :=
  roundedVertexPath ρ (P z) u

theorem openArcRoundedFamily_eq_local
    (data : OpenArcRoundedData ρ P) (i : ℤ) {z : ℝ × ℝ} {u : ℝ}
    (hu : u ∈ Ioo ((i : ℝ) - 1 + data.δ) ((i : ℝ) + 1 - data.δ)) :
    openArcRoundedFamily ρ P z u =
      roundedCorner ρ (P z i) (P z i - P z (i - 1))
        (P z (i + 1) - P z i) (u - i) := by
  exact roundedVertexPath_eq_local (P z) data.delta_pos (by linarith [data.delta_quarter])
    data.profile_tail data.profile_bound i hu

theorem contDiff_openArcRoundedFamily
    (data : OpenArcRoundedData ρ P) :
    ContDiff ℝ ∞
      (fun x : (ℝ × ℝ) × ℝ => openArcRoundedFamily ρ P x.1 x.2) := by
  simpa only [openArcRoundedFamily] using
    (contDiff_roundedVertexPath (P := P) data.delta_pos
      (by linarith [data.delta_quarter]) data.profile_tail data.profile_bound
      data.profile_smooth data.vertices_smooth)

theorem openArcRoundedFamily_local_injective
    (data : OpenArcRoundedData ρ P) (z : ℝ × ℝ) :
    ∀ s t : ℝ, |s - t| < 1 / 4 →
      openArcRoundedFamily ρ P z s = openArcRoundedFamily ρ P z t → s = t := by
  intro s t hst heq
  let i : ℤ := ⌊s + 1 / 2⌋
  have hlo : (i : ℝ) ≤ s + 1 / 2 := Int.floor_le _
  have hhi : s + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
  rcases abs_lt.mp hst with ⟨hstlo, hsthi⟩
  have hs : s ∈ Ioo ((i : ℝ) - 1 + data.δ) ((i : ℝ) + 1 - data.δ) := by
    constructor <;> linarith [data.delta_quarter]
  have ht : t ∈ Ioo ((i : ℝ) - 1 + data.δ) ((i : ℝ) + 1 - data.δ) := by
    constructor <;> linarith [data.delta_quarter]
  obtain ⟨ℓ, hu, hv⟩ := data.corner_functional z i
  have hinj := (strictMono_roundedCorner_projection
    (P z i) (P z i - P z (i - 1)) (P z (i + 1) - P z i)
    (data.profile_smooth.differentiable (by simp)) data.profile_derivative ℓ hu hv).2.2
  have hsEq := openArcRoundedFamily_eq_local data i (z := z) hs
  have htEq := openArcRoundedFamily_eq_local data i (z := z) ht
  have hparam : s - (i : ℝ) = t - i := hinj (by
    rw [← hsEq, ← htEq]
    exact heq)
  linarith

theorem openArcRoundedFamily_regular
    (data : OpenArcRoundedData ρ P) (z : ℝ × ℝ) (t : ℝ) :
    deriv (openArcRoundedFamily ρ P z) t ≠ 0 := by
  let i : ℤ := ⌊t + 1 / 2⌋
  have hlo : (i : ℝ) ≤ t + 1 / 2 := Int.floor_le _
  have hhi : t + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
  have ht : t ∈ Ioo ((i : ℝ) - 1 + data.δ) ((i : ℝ) + 1 - data.δ) := by
    constructor <;> linarith [data.delta_quarter]
  obtain ⟨ℓ, hu, hv⟩ := data.corner_functional z i
  let Γ := roundedCorner ρ (P z i) (P z i - P z (i - 1))
    (P z (i + 1) - P z i)
  have hΓ := hasDerivAt_roundedCorner (P z i) (P z i - P z (i - 1))
    (P z (i + 1) - P z i) ((data.profile_smooth.differentiable (by simp)) (t - i))
  have hΓ' : HasDerivAt Γ (deriv Γ (t - i)) (t - i) :=
    hΓ.congr_deriv hΓ.deriv.symm
  have htrans : HasDerivAt (fun s : ℝ => Γ (s - i))
      (deriv Γ (t - i)) t := by
    simpa only [Function.comp_def, one_smul, id_eq] using
      hΓ'.scomp t ((hasDerivAt_id t).sub_const (i : ℝ))
  have hactual : HasDerivAt (openArcRoundedFamily ρ P z)
      (deriv Γ (t - i)) t := by
    apply htrans.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact openArcRoundedFamily_eq_local data i (z := z) hs
  rw [hactual.deriv]
  intro hz
  have hpos := (strictMono_roundedCorner_projection
    (P z i) (P z i - P z (i - 1)) (P z (i + 1) - P z i)
    (data.profile_smooth.differentiable (by simp)) data.profile_derivative ℓ hu hv).1
    (t - i)
  change 0 < ℓ (deriv Γ (t - i)) at hpos
  rw [hz, map_zero] at hpos
  exact (lt_irrefl 0) hpos

theorem openArcRoundedFamily_fderiv_regular
    (data : OpenArcRoundedData ρ P) (z : ℝ × ℝ) (t : ℝ) :
    fderiv ℝ (openArcRoundedFamily ρ P z) t 1 ≠ 0 := by
  simpa only [fderiv_apply_one_eq_deriv] using
    openArcRoundedFamily_regular data z t

theorem openArcRoundedFamily_injective_of_separation
    (data : OpenArcRoundedData ρ P)
    (L : (ℝ × ℝ) → ℝ → (ℝ × ℝ))
    {ε : ℝ}
    (hclose : ∀ z u, dist (openArcRoundedFamily ρ P z u) (L z u) ≤ ε)
    (hsep : ∀ z s t, 1 / 4 ≤ |s - t| →
      2 * ε < dist (L z s) (L z t)) :
    ∀ z, Injective (openArcRoundedFamily ρ P z) := by
  intro z s t heq
  by_cases hsmall : |s - t| < 1 / 4
  · exact openArcRoundedFamily_local_injective data z s t hsmall heq
  · have hfar : 1 / 4 ≤ |s - t| := le_of_not_gt hsmall
    have hmargin := hsep z s t hfar
    have hdist : dist (L z s) (L z t) ≤ 2 * ε := by
      calc
        dist (L z s) (L z t) ≤
            dist (L z s) (openArcRoundedFamily ρ P z s) +
              dist (openArcRoundedFamily ρ P z s)
                (openArcRoundedFamily ρ P z t) +
              dist (openArcRoundedFamily ρ P z t) (L z t) :=
          dist_triangle4 _ _ _ _
        _ ≤ ε + 0 + ε := by
          rw [heq, dist_self]
          have hs := hclose z s
          rw [dist_comm, heq] at hs
          have ht := hclose z t
          linarith
        _ = 2 * ε := by ring
    linarith

theorem openArcRoundedFamily_axis_tail
    (data : OpenArcRoundedData ρ P) (z : ℝ × ℝ) (u : ℝ)
    (hu : data.tail_radius + 4 ≤ |u|) :
    openArcRoundedFamily ρ P z u = (u, 0) := by
  let i : ℤ := ⌊u + 1 / 2⌋
  have hlo : (i : ℝ) ≤ u + 1 / 2 := Int.floor_le _
  have hhi : u + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
  have hcenter : |u - (i : ℝ)| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hshift (j : ℤ) (hj : |j - i| ≤ 1) :
      data.tail_radius + 2 ≤ |(j : ℝ)| := by
    have hdist : |u - (j : ℝ)| ≤ 3 / 2 := by
      calc
          |u - (j : ℝ)| ≤ |u - (i : ℝ)| + |(i : ℝ) - (j : ℝ)| :=
          _root_.abs_sub_le _ _ _
        _ ≤ 3 / 2 := by
          have hji : |(i : ℝ) - (j : ℝ)| ≤ 1 := by
            rw [abs_sub_comm]
            exact_mod_cast hj
          linarith
    have hsum : |u| ≤ |u - (j : ℝ)| + |(j : ℝ)| := by
      calc
        |u| = |(u - (j : ℝ)) + (j : ℝ)| := by ring_nf
        _ ≤ |u - (j : ℝ)| + |(j : ℝ)| := abs_add_le _ _
    linarith
  have hi0 : data.tail_radius + 2 ≤ |(i : ℝ)| := hshift i (by simp)
  have him : data.tail_radius + 2 ≤ |((i - 1 : ℤ) : ℝ)| := hshift (i - 1) (by simp)
  have hip : data.tail_radius + 2 ≤ |((i + 1 : ℤ) : ℝ)| := hshift (i + 1) (by simp)
  have hPi := data.vertex_tail z i hi0
  have hPim := data.vertex_tail z (i - 1) him
  have hPip := data.vertex_tail z (i + 1) hip
  have htu : u ∈ Ioo ((i : ℝ) - 1 + data.δ) ((i : ℝ) + 1 - data.δ) := by
    constructor <;> linarith [data.delta_quarter, hlo, hhi]
  rw [openArcRoundedFamily_eq_local data i (z := z) htu, hPi, hPim, hPip]
  dsimp only [roundedCorner]
  change
    (((i : ℝ), 0) : ℝ × ℝ) +
        (((u - (i : ℝ) - ρ (u - (i : ℝ))) / 2) •
          ((((i : ℝ), 0) : ℝ × ℝ) - (((i - 1 : ℤ) : ℝ), 0))) +
        (((u - (i : ℝ) + ρ (u - (i : ℝ))) / 2) •
          ((((i + 1 : ℤ) : ℝ), 0) - (((i : ℝ), 0) : ℝ × ℝ))) = (u, 0)
  simp only [Int.cast_sub, Int.cast_add]
  ext <;> dsimp <;> ring

end PoincareConjecture.M25.Topology3D
