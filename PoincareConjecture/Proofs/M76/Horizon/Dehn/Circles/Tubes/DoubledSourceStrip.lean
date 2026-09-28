import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SourceStripFibers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SourceStripPeriod

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

noncomputable def doubledSourceStrip {E : Type*} (sign : Bool) (a b : ℝ)
    (phi : Fin 2 → P2 → E) (z : P2) : E :=
  if z.2 ≤ b then phi 0 ((if sign then z.1 else -z.1), z.2)
  else phi 1 (z.1, z.2 - (b - a))

private theorem transverse_sign_mem (sign : Bool) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    (if sign then u else -u) ∈ Icc (-1 : ℝ) 1 := by
  cases sign
  · change -u ∈ Icc (-1 : ℝ) 1
    constructor <;> linarith [hu.1, hu.2]
  · exact hu

theorem doubledSourceStrip_first {E : Type*} (sign : Bool) (a b : ℝ)
    (phi : Fin 2 → P2 → E) {z : P2} (hz : z.2 ≤ b) :
    doubledSourceStrip sign a b phi z = phi 0 ((if sign then z.1 else -z.1), z.2) :=
  if_pos hz

theorem doubledSourceStrip_second {E : Type*} (sign : Bool) {a b : ℝ}
    (phi : Fin 2 → P2 → E)
    (hclose : ∀ u ∈ Icc (-1 : ℝ) 1, phi 1 (u, a) = phi 0 ((if sign then u else -u), b))
    {z : P2} (hu : z.1 ∈ Icc (-1 : ℝ) 1) (hz : b ≤ z.2) :
    doubledSourceStrip sign a b phi z = phi 1 (z.1, z.2 - (b - a)) := by
  by_cases h : z.2 ≤ b
  · have hzb : z.2 = b := le_antisymm h hz
    rw [doubledSourceStrip_first sign a b phi h, hzb]
    simpa using (hclose z.1 hu).symm
  · exact if_neg h

private theorem rectangle_affine_finitePL {a b : ℝ} (hab : a < b)
    (A : P2 →ᴬ[ℝ] P2) : FinitePiecewiseAffineOn A (Icc (-1 : ℝ) 1 ×ˢ Icc a b) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    HeightBox.rectangle_ballPair (show (0 : ℝ) < 1 by norm_num) hab
  exact ⟨K, hK, hKs, K.affineOnFaces_affine A⟩

theorem doubledSourceStrip_finitePL
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sign : Bool) {a b : ℝ} (hab : a < b) (phi : Fin 2 → P2 → E)
    (hPL : ∀ j, FinitePiecewiseAffineOn (phi j) (Icc (-1 : ℝ) 1 ×ˢ Icc a b))
    (hclose : ∀ u ∈ Icc (-1 : ℝ) 1, phi 1 (u, a) = phi 0 ((if sign then u else -u), b)) :
    FinitePiecewiseAffineOn (doubledSourceStrip sign a b phi)
      (Icc (-1 : ℝ) 1 ×ˢ Icc a (2 * b - a)) := by
  let A : P2 →ᴬ[ℝ] P2 :=
    (((if sign then (1 : ℝ) else -1) • ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  have hA (z : P2) : A z = ((if sign then z.1 else -z.1), z.2) := by
    cases sign <;> simp [A]
  let B : P2 →ᴬ[ℝ] P2 := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap.prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap - ContinuousAffineMap.const ℝ P2 (b - a))
  have hB (z : P2) : B z = (z.1, z.2 - (b - a)) := rfl
  have hfirst : FinitePiecewiseAffineOn (doubledSourceStrip sign a b phi)
      (Icc (-1 : ℝ) 1 ×ˢ Icc a b) := by
    have hmap : MapsTo A (Icc (-1 : ℝ) 1 ×ˢ Icc a b) (Icc (-1 : ℝ) 1 ×ˢ Icc a b) := by
      intro z hz
      rw [hA]
      exact ⟨transverse_sign_mem sign hz.1, hz.2⟩
    exact ((hPL 0).comp (rectangle_affine_finitePL hab A) hmap).congr
      (fun z hz => by rw [Function.comp_apply, hA, doubledSourceStrip_first sign a b phi hz.2.2])
  have hsecond : FinitePiecewiseAffineOn (doubledSourceStrip sign a b phi)
      (Icc (-1 : ℝ) 1 ×ˢ Icc b (2 * b - a)) := by
    have hmap : MapsTo B (Icc (-1 : ℝ) 1 ×ˢ Icc b (2 * b - a))
        (Icc (-1 : ℝ) 1 ×ˢ Icc a b) := by
      intro z hz
      rw [hB]
      exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
    exact ((hPL 1).comp (rectangle_affine_finitePL (by linarith) B) hmap).congr
      (fun z hz => by rw [Function.comp_apply, hB,
        doubledSourceStrip_second sign phi hclose hz.1 hz.2.1])
  let S (j : Bool) := Icc (-1 : ℝ) 1 ×ˢ (if j then Icc a b else Icc b (2 * b - a))
  have hlocal (j : Bool) : FinitePiecewiseAffineOn (doubledSourceStrip sign a b phi) (S j) := by
    cases j
    · exact hsecond
    · exact hfirst
  have hS : (⋃ j, S j) = Icc (-1 : ℝ) 1 ×ˢ Icc a (2 * b - a) := by
    ext z
    simp only [S, mem_iUnion, Bool.exists_bool, Bool.false_eq_true, if_false, if_true,
      mem_prod, mem_Icc]
    constructor
    · rintro (⟨hu, ht⟩ | ⟨hu, ht⟩) <;> exact ⟨hu, by constructor <;> linarith [ht.1, ht.2]⟩
    · rintro ⟨hu, ht⟩
      by_cases h : z.2 ≤ b
      · exact Or.inr ⟨hu, ht.1, h⟩
      · exact Or.inl ⟨hu, le_of_not_ge h, ht.2⟩
  exact hS ▸ FinitePiecewiseAffineOn.iUnion hlocal

set_option maxHeartbeats 800000 in

theorem doubledSourceStrip_fibers {E : Type*}
    (sign : Bool) {a b : ℝ} (hab : a < b) (phi : Fin 2 → P2 → E)
    (hfib : ∀ j k z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      ∀ w, w ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b →
      (phi j z = phi k w ↔ (j = k ∧ z = w) ∨
        (z.2 = a ∧ w.2 = b ∧ k = j.rev ∧ w.1 = (if sign then z.1 else -z.1)) ∨
        (w.2 = a ∧ z.2 = b ∧ j = k.rev ∧ z.1 = (if sign then w.1 else -w.1)))) :
    ∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a (2 * b - a),
      ∀ w ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a (2 * b - a),
      doubledSourceStrip sign a b phi z = doubledSourceStrip sign a b phi w ↔
        z.1 = w.1 ∧ (z.2 = w.2 ∨ (z.2 = a ∧ w.2 = 2 * b - a) ∨
          (w.2 = a ∧ z.2 = 2 * b - a)) := by
  intro z hz w hw
  have hfirst (v : P2) (hv : v ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a (2 * b - a)) (hvB : v.2 ≤ b) :
      ((if sign then v.1 else -v.1), v.2) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b :=
    ⟨transverse_sign_mem sign hv.1, hv.2.1, hvB⟩
  have hsecond (v : P2) (hv : v ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a (2 * b - a)) (hvB : ¬v.2 ≤ b) :
      (v.1, v.2 - (b - a)) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b :=
    ⟨hv.1, by constructor <;> linarith [hv.2.1, hv.2.2]⟩
  by_cases hzB : z.2 ≤ b <;> by_cases hwB : w.2 ≤ b
  · simp only [doubledSourceStrip, if_pos hzB, if_pos hwB]
    rw [hfib 0 0 _ (hfirst z hz hzB) _ (hfirst w hw hwB)]
    cases sign <;> simp [Fin.rev] <;> grind
  · simp only [doubledSourceStrip, if_pos hzB, if_neg hwB]
    rw [hfib 0 1 _ (hfirst z hz hzB) _ (hsecond w hw hwB)]
    cases sign <;> simp [Fin.rev] <;> grind
  · simp only [doubledSourceStrip, if_neg hzB, if_pos hwB]
    rw [hfib 1 0 _ (hsecond z hz hzB) _ (hfirst w hw hwB)]
    cases sign <;> simp [Fin.rev] <;> grind
  · simp only [doubledSourceStrip, if_neg hzB, if_neg hwB]
    rw [hfib 1 1 _ (hsecond z hz hzB) _ (hsecond w hw hwB)]
    cases sign <;> simp [Fin.rev] <;> grind

theorem doubledSourceStrip_image {E : Type*}
    (sign : Bool) {a b : ℝ} (hab : a < b) (phi : Fin 2 → P2 → E)
    (hclose : ∀ u ∈ Icc (-1 : ℝ) 1, phi 1 (u, a) = phi 0 ((if sign then u else -u), b)) :
    doubledSourceStrip sign a b phi '' (Icc (-1 : ℝ) 1 ×ˢ Icc a (2 * b - a)) =
      (phi 0 '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b)) ∪
        (phi 1 '' (Icc (-1 : ℝ) 1 ×ˢ Icc a b)) := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    by_cases h : z.2 ≤ b
    · exact Or.inl ⟨((if sign then z.1 else -z.1), z.2),
        ⟨transverse_sign_mem sign hz.1, hz.2.1, h⟩,
        (doubledSourceStrip_first sign a b phi h).symm⟩
    · exact Or.inr ⟨(z.1, z.2 - (b - a)),
        ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩, (if_neg h).symm⟩
  · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · refine ⟨((if sign then z.1 else -z.1), z.2),
        ⟨transverse_sign_mem sign hz.1, hz.2.1, by linarith [hz.2.2]⟩, ?_⟩
      rw [doubledSourceStrip_first sign a b phi
        (z := ((if sign then z.1 else -z.1), z.2)) hz.2.2]
      cases sign <;> simp
    · refine ⟨(z.1, z.2 + (b - a)),
        ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩, ?_⟩
      rw [doubledSourceStrip_second sign phi hclose
        (z := (z.1, z.2 + (b - a))) hz.1 (by dsimp; linarith [hz.2.1])]
      simp

theorem doubledSourceStrip_axis {E : Type*}
    (sign : Bool) {a b : ℝ} (phi : Fin 2 → P2 → E) (A : Set E)
    (haxis : ∀ j z, z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a b → (phi j z ∈ A ↔ z.1 = 0))
    (z : P2) (hz : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc a (2 * b - a)) :
    doubledSourceStrip sign a b phi z ∈ A ↔ z.1 = 0 := by
  by_cases h : z.2 ≤ b
  · rw [doubledSourceStrip_first sign a b phi h,
      haxis 0 ((if sign then z.1 else -z.1), z.2) ⟨transverse_sign_mem sign hz.1, hz.2.1, h⟩]
    cases sign <;> simp
  · rw [show doubledSourceStrip sign a b phi z = phi 1 (z.1, z.2 - (b - a)) from if_neg h]
    exact haxis 1 _ ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩

end PoincareConjecture.M76.Dehn
