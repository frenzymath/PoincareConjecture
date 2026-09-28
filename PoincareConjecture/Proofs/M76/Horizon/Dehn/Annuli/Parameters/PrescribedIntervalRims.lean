import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.CutRectangleExtension
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.CutRectangleQuotient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "I" => Icc (0 : ℝ) 1
local notation "P2" => (ℝ × ℝ)

private theorem exists_unit_period_rectangle :
    ∃ A : (I ×ˢ I : Set P2) ≃ₜ rectangle (4 * 8) 1, A.IsFinitePL ∧
      ∀ z : (I ×ˢ I : Set P2), (A z : P2) = (32 * (z : P2).1, 2 * (z : P2).2 - 1) := by
  let a : P2 →ᴬ[ℝ] P2 :=
    ((32 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).prod
      ((2 : ℝ) • (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap -
        ContinuousAffineMap.const ℝ P2 1)
  have ha (z : P2) : a z = (32 * z.1, 2 * z.2 - 1) := rfl
  have hb := (isFinitePLBallPair_Icc zero_lt_one).prod (isFinitePLBallPair_Icc zero_lt_one)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hb
  have hPL : FinitePiecewiseAffineOn a (I ×ˢ I : Set P2) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine a⟩
  have hinj : InjOn a (I ×ˢ I : Set P2) := by
    intro x _ y _ h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    change 32 * x.1 = 32 * y.1 at hx
    change 2 * x.2 - 1 = 2 * y.2 - 1 at hy
    exact Prod.ext (by linarith) (by linarith)
  have himage : a '' (I ×ˢ I : Set P2) = rectangle (4 * 8) 1 := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      change (32 * z.1 ∈ Icc 0 (4 * 8)) ∧ (2 * z.2 - 1 ∈ Icc (-1) 1)
      constructor <;> constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
    · intro z hz
      refine ⟨(z.1 / 32, (z.2 + 1) / 2), ⟨?_, ?_⟩, ?_⟩
      · constructor <;> linarith [hz.1.1, hz.1.2]
      · constructor <;> linarith [hz.2.1, hz.2.2]
      · rw [ha]
        apply Prod.ext <;> dsimp <;> ring
  obtain ⟨A, hA, hAv⟩ := hPL.exists_homeomorph_image hinj
  exact ⟨A.trans (Homeomorph.setCongr himage), hA.setCongr rfl himage, hAv⟩

theorem exists_annulus_homeomorph_prescribed_interval_rims
    (e : Bool → I ≃ₜ I) (he : ∀ b, (e b).IsFinitePL)
    (hzero : ∀ b, (e b ⟨0, by norm_num⟩ : ℝ) = 0)
    (hone : ∀ b, (e b ⟨1, by norm_num⟩ : ℝ) = 1) :
    ∃ A : squareAnnulus 8 1 ≃ₜ squareAnnulus 8 1, A.IsFinitePL ∧
      ∀ (b : Bool) (s : I),
        (A ⟨annulusMap 8 (by norm_num)
          (((32 * (s : ℝ) : ℝ) : AddCircle (4 * (8 : ℝ))), if b then 1 else -1),
          _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _
            ⟨if b then 1 else -1, by cases b <;> norm_num⟩⟩ : P2) =
        annulusMap 8 (by norm_num)
          (((32 * (e b s : ℝ) : ℝ) : AddCircle (4 * (8 : ℝ))), if b then 1 else -1) := by
  obtain ⟨H, hH, hB, hT, hL, hR⟩ := exists_finitePL_cut_rectangle_extension
    (e false) (e true) (he false) (he true) (hzero false) (hone false)
    (hzero true) (hone true)
  obtain ⟨C, hC, hCv⟩ := exists_unit_period_rectangle
  let G : rectangle (4 * 8) 1 ≃ₜ rectangle (4 * 8) 1 := C.symm.trans (H.trans C)
  have hG : G.IsFinitePL := hC.symm.trans (hH.trans hC)
  have hGC (w : (I ×ˢ I : Set P2)) : G (C w) = C (H w) := by simp [G]
  have hsides (a : ℝ) (ha : a = 0 ∨ a = 1)
      (hside : ∀ t : I, (H ⟨(a, t), by rcases ha with rfl | rfl <;> norm_num, t.property⟩ : P2) = (a, (t : ℝ)))
      (u : Icc (-1 : ℝ) 1) :
      (G ⟨(32 * a, u), by rcases ha with rfl | rfl <;> norm_num, u.property⟩ : P2) =
        (32 * a, (u : ℝ)) := by
    let t : I := ⟨((u : ℝ) + 1) / 2, by constructor <;> linarith [u.property.1, u.property.2]⟩
    let w : (I ×ˢ I : Set P2) := ⟨(a, t), by rcases ha with rfl | rfl <;> norm_num, t.property⟩
    have hCw : C w = ⟨(32 * a, u), by rcases ha with rfl | rfl <;> norm_num, u.property⟩ := by
      apply Subtype.ext
      rw [hCv]
      apply Prod.ext
      · rfl
      · dsimp [w, t]
        ring
    rw [← hCw, hGC, hCv, hside t]
    apply Prod.ext
    · rfl
    · dsimp [t]
      ring
  have hleft : ∀ u : Icc (-1 : ℝ) 1,
      (G ⟨(0, u), by norm_num, u.property⟩ : P2) = (0, (u : ℝ)) := by
    intro u
    simpa only [mul_zero] using hsides 0 (Or.inl rfl) hL u
  have hright : ∀ u : Icc (-1 : ℝ) 1,
      (G ⟨(32, u), by norm_num, u.property⟩ : P2) = (32, (u : ℝ)) := by
    intro u
    simpa only [mul_one] using hsides 1 (Or.inr rfl) hR u
  obtain ⟨A, hA, hAv⟩ := exists_annulus_homeomorph_of_cut_rectangle
    (L := 8) (d := 1) (by norm_num) (by norm_num) G hG hleft
      (by simpa only [show (4 : ℝ) * 8 = 32 by norm_num] using hright)
  refine ⟨A, hA, ?_⟩
  intro b s
  have hs : 32 * (s : ℝ) ∈ Icc (0 : ℝ) (4 * 8) := by
    constructor <;> linarith [s.property.1, s.property.2]
  rw [hAv _ hs ⟨if b then 1 else -1, by cases b <;> norm_num⟩]
  have hbottom : (G ⟨(32 * (s : ℝ), -1), hs, by norm_num⟩ : P2) =
      (32 * (e false s : ℝ), -1) := by
    have hc : C ⟨(s, 0), s.property, by norm_num⟩ =
        ⟨(32 * (s : ℝ), -1), hs, by norm_num⟩ := by
      apply Subtype.ext
      simpa using hCv ⟨(s, 0), s.property, by norm_num⟩
    rw [← hc, hGC, hCv, hB]
    norm_num
  have htop : (G ⟨(32 * (s : ℝ), 1), hs, by norm_num⟩ : P2) =
      (32 * (e true s : ℝ), 1) := by
    have hc : C ⟨(s, 1), s.property, by norm_num⟩ =
        ⟨(32 * (s : ℝ), 1), hs, by norm_num⟩ := by
      apply Subtype.ext
      convert hCv ⟨(s, 1), s.property, by norm_num⟩ using 1
      norm_num
    rw [← hc, hGC, hCv, hT]
    norm_num
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true]
  · rw [hbottom]
  · rw [htop]

end PoincareConjecture.M76.Dehn
