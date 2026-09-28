import PoincareConjecture.Proofs.M76.Mathlib.PositiveSlopeBend
import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine

set_option autoImplicit false

open Set Geometry

namespace PLStrip

def stripMap (a b : ℝ) (q : ℝ × ℝ) : ℝ × ℝ :=
  (a * q.2 + bend a b (q.1 - q.2), q.2)

noncomputable def stripHomeomorph {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := stripMap a b
  invFun q := (q.2 + bend a⁻¹ b⁻¹ (q.1 - a * q.2), q.2)
  left_inv q := by
    refine Prod.ext ?_ (by rfl)
    change q.2 + bend a⁻¹ b⁻¹ (a * q.2 + bend a b (q.1 - q.2) - a * q.2) = q.1
    rw [add_sub_cancel_left, bend_inv_bend ha hb]
    ring
  right_inv q := by
    refine Prod.ext ?_ (by rfl)
    change a * q.2 + bend a b (q.2 + bend a⁻¹ b⁻¹ (q.1 - a * q.2) - q.2) = q.1
    rw [add_sub_cancel_left]
    have h := bend_inv_bend (inv_pos.mpr ha) (inv_pos.mpr hb) (q.1 - a * q.2)
    simp only [inv_inv] at h
    rw [h]
    ring
  continuous_toFun :=
    ((continuous_const.mul continuous_snd).add
      ((continuous_bend a b).comp (continuous_fst.sub continuous_snd))).prodMk continuous_snd
  continuous_invFun :=
    (continuous_snd.add ((continuous_bend a⁻¹ b⁻¹).comp
      (continuous_fst.sub (continuous_const.mul continuous_snd)))).prodMk continuous_snd

theorem strictMono_stripMap_fst {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    StrictMono (fun s => (stripMap a b (s, t)).1) := by
  intro x y hxy
  change a * t + bend a b (x - t) < a * t + bend a b (y - t)
  linarith [strictMono_bend ha hb (sub_lt_sub_right hxy t)]

theorem stripMap_left (a b : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    stripMap a b (0, t) = (0, t) := by
  refine Prod.ext ?_ (by rfl)
  change a * t + bend a b (0 - t) = 0
  rw [bend_of_nonpos a b (sub_nonpos.mpr ht)]
  ring

theorem stripMap_right (a b : ℝ) {t : ℝ} (ht : t ≤ 1) :
    stripMap a b (1, t) = (a * t + b * (1 - t), t) := by
  refine Prod.ext ?_ (by rfl)
  change a * t + bend a b (1 - t) = a * t + b * (1 - t)
  rw [bend_of_nonneg a b (sub_nonneg.mpr ht)]

theorem stripMap_bottom (a b : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    stripMap a b (s, 0) = (b * s, 0) := by
  refine Prod.ext ?_ (by rfl)
  change a * 0 + bend a b (s - 0) = b * s
  rw [mul_zero, zero_add, sub_zero, bend_of_nonneg a b hs]

theorem stripMap_top (a b : ℝ) {s : ℝ} (hs : s ≤ 1) :
    stripMap a b (s, 1) = (a * s, 1) := by
  refine Prod.ext ?_ (by rfl)
  change a * 1 + bend a b (s - 1) = a * s
  rw [bend_of_nonpos a b (sub_nonpos.mpr hs)]
  ring

theorem finitePiecewiseAffineOn_stripMap (a b : ℝ)
    (K : SimplicialComplex ℝ (ℝ × ℝ)) (hK : K.faces.Finite) :
    FinitePiecewiseAffineOn (stripMap a b) K.space := by
  classical
  let X : (ℝ × ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  let Y : (ℝ × ℝ) →ᴬ[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  let A := (X - Y).toAffineMap
  let N := hK.toFinset.sup Finset.card
  have hN (s : Finset (ℝ × ℝ)) (hs : s ∈ K.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨L, hL, hLK, _, hLA⟩ :=
    K.exists_subdivision_respectsAffineHyperplanes hK hN {A}
  refine ⟨L, hL, hLK.space_eq, fun s hs => ?_⟩
  rcases hLA A (Finset.mem_singleton_self A) s hs with hlo | hhi
  · refine ⟨(a • X).prod Y, fun q hq => ?_⟩
    refine Prod.ext ?_ (by rfl)
    change a * q.2 + bend a b (q.1 - q.2) = a * q.1
    have hqA : q.1 - q.2 ≤ 0 := hlo q hq
    rw [bend_of_nonpos a b hqA]
    ring
  · refine ⟨(a • Y + b • (X - Y)).prod Y, fun q hq => ?_⟩
    refine Prod.ext ?_ (by rfl)
    change a * q.2 + bend a b (q.1 - q.2) = a * q.2 + b * (q.1 - q.2)
    have hqA : 0 ≤ q.1 - q.2 := hhi q hq
    rw [bend_of_nonneg a b hqA]

theorem stripMap_image_square {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    stripMap a b '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) =
      {q : ℝ × ℝ | q.2 ∈ Icc 0 1 ∧ 0 ≤ q.1 ∧ q.1 ≤ a * q.2 + b * (1 - q.2)} := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hmono := (strictMono_stripMap_fst ha hb p.2).monotone
    have hlo := hmono hp.1.1
    have hhi := hmono hp.1.2
    dsimp only at hlo hhi
    rw [stripMap_left a b hp.2.1] at hlo
    rw [stripMap_right a b hp.2.2] at hhi
    exact ⟨hp.2, hlo, hhi⟩
  · rintro ⟨hqt, hqx, hqwidth⟩
    let p := (stripHomeomorph ha hb).symm q
    have hpq : stripMap a b p = q := (stripHomeomorph ha hb).apply_symm_apply q
    have hpt : p.2 = q.2 := rfl
    have hmono := strictMono_stripMap_fst ha hb p.2
    have hleft : (stripMap a b (0, p.2)).1 ≤ (stripMap a b (p.1, p.2)).1 := by
      rw [stripMap_left a b (hpt ▸ hqt.1), Prod.mk.eta, hpq]
      exact hqx
    have hright : (stripMap a b (p.1, p.2)).1 ≤ (stripMap a b (1, p.2)).1 := by
      rw [stripMap_right a b (hpt ▸ hqt.2), Prod.mk.eta, hpq, hpt]
      exact hqwidth
    exact ⟨p, ⟨⟨hmono.le_iff_le.mp hleft, hmono.le_iff_le.mp hright⟩, hpt ▸ hqt⟩, hpq⟩

end PLStrip
