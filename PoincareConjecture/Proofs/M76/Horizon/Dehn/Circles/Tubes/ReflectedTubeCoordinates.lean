import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SignedAxisMonodromy
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.ReflectionTubeDoubling










set_option autoImplicit false
open Set Geometry
open Dehn

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

noncomputable def reflectedTubeTransverse (closing : SignedAxisPermutation)
    (d : ℝ) (hd : 0 < d) : P2 ≃L[ℝ] P2 :=
  (LinearEquiv.smulOfNeZero ℝ P2 d⁻¹ (inv_ne_zero hd.ne')).toContinuousLinearEquiv.trans
    closing.reflectionCoordinates

theorem reflectedTubeTransverse_apply (closing : SignedAxisPermutation)
    (d : ℝ) (hd : 0 < d) (x : P2) :
    reflectedTubeTransverse closing d hd x = closing.reflectionCoordinates (d⁻¹ • x) := rfl

theorem reflectedTubeTransverse_mem (closing : SignedAxisPermutation)
    (d : ℝ) (hd : 0 < d) (x : P2) :
    reflectedTubeTransverse closing d hd x ∈ signedTubeDiamond ↔
      x ∈ Icc (-d) d ×ˢ Icc (-d) d := by
  rw [reflectedTubeTransverse_apply, closing.reflectionCoordinates_mem]
  change (d⁻¹ * x.1 ∈ Icc (-1 : ℝ) 1 ∧ d⁻¹ * x.2 ∈ Icc (-1 : ℝ) 1) ↔ _
  simp only [mem_prod, mem_Icc, inv_mul_eq_div, le_div_iff₀ hd, div_le_iff₀ hd,
    neg_one_mul, one_mul]

theorem reflectedTubeTransverse_conjugate (closing : SignedAxisPermutation)
    (hswap : closing.swap = true) (hsign : closing.sign 0 = closing.sign 1)
    (d : ℝ) (hd : 0 < d) (x : P2) :
    closing.linear (reflectedTubeTransverse closing d hd x) =
      reflectedTubeTransverse closing d hd (x.1, -x.2) := by
  rw [reflectedTubeTransverse_apply, closing.reflectionCoordinates_conjugate hswap hsign,
    reflectedTubeTransverse_apply]
  congr 1
  ext <;> simp [smul_eq_mul]

noncomputable def reflectedTubeCoordinates (closing : SignedAxisPermutation)
    (a b L d : ℝ) (hab : a < b) (hL : 0 < L) (hd : 0 < d) : C3 ≃ᴬ[ℝ] C3 :=
  let time : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.smulOfNeZero ℝ ℝ ((b - a) / (2 * L))
      (ne_of_gt (div_pos (sub_pos.mpr hab) (by positivity)))).toContinuousLinearEquiv
  (reflectedTubeTransverse closing d hd).toContinuousAffineEquiv.prodCongr
    (time.toContinuousAffineEquiv.trans
      (ContinuousAffineEquiv.constVAdd ℝ ℝ a))

theorem reflectedTubeCoordinates_apply (closing : SignedAxisPermutation)
    (a b L d : ℝ) (hab : a < b) (hL : 0 < L) (hd : 0 < d) (z : C3) :
    reflectedTubeCoordinates closing a b L d hab hL hd z =
      (reflectedTubeTransverse closing d hd z.1, a + (b - a) / (2 * L) * z.2) := rfl

private theorem reflected_time_end {a b L : ℝ} (hL : 0 < L) :
    a + (b - a) / (2 * L) * (2 * L) = b := by
  rw [div_mul_cancel₀ _ (by positivity : 2 * L ≠ 0)]
  ring

theorem reflectedTubeCoordinates_time_iff (closing : SignedAxisPermutation)
    (a b L d : ℝ) (hab : a < b) (hL : 0 < L) (hd : 0 < d) (z : C3) :
    (reflectedTubeCoordinates closing a b L d hab hL hd z).2 ∈ Icc a b ↔
      z.2 ∈ Icc 0 (2 * L) := by
  rw [reflectedTubeCoordinates_apply]
  have hk : 0 < (b - a) / (2 * L) := div_pos (sub_pos.mpr hab) (by positivity)
  have hend := reflected_time_end (a := a) (b := b) hL
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> nlinarith

theorem reflectedTubeCoordinates_mem (closing : SignedAxisPermutation)
    (a b L d : ℝ) (hab : a < b) (hL : 0 < L) (hd : 0 < d) (z : C3) :
    reflectedTubeCoordinates closing a b L d hab hL hd z ∈ signedTubeDiamond ×ˢ Icc a b ↔
      z ∈ singleReflectionTube L d := by
  change (_ ∈ signedTubeDiamond ∧ _ ∈ Icc a b) ↔ _
  rw [reflectedTubeCoordinates_time_iff]
  change (reflectedTubeTransverse closing d hd z.1 ∈ signedTubeDiamond ∧ _) ↔ _
  rw [reflectedTubeTransverse_mem]
  rfl

theorem reflectedTubeCoordinates_image (closing : SignedAxisPermutation)
    (a b L d : ℝ) (hab : a < b) (hL : 0 < L) (hd : 0 < d) :
    reflectedTubeCoordinates closing a b L d hab hL hd '' singleReflectionTube L d =
      signedTubeDiamond ×ˢ Icc a b := by
  let e := reflectedTubeCoordinates closing a b L d hab hL hd
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (reflectedTubeCoordinates_mem closing a b L d hab hL hd x).mpr hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (reflectedTubeCoordinates_mem closing a b L d hab hL hd (e.symm y)).mp
    change e (e.symm y) ∈ signedTubeDiamond ×ˢ Icc a b
    simpa only [e.apply_symm_apply] using hy

theorem reflectedTubeTransverse_image (closing : SignedAxisPermutation)
    (d : ℝ) (hd : 0 < d) :
    reflectedTubeTransverse closing d hd '' (Icc (-d) d ×ˢ Icc (-d) d) =
      signedTubeDiamond := by
  let e := reflectedTubeTransverse closing d hd
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (reflectedTubeTransverse_mem closing d hd x).mpr hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (reflectedTubeTransverse_mem closing d hd (e.symm y)).mp
    change e (e.symm y) ∈ signedTubeDiamond
    simpa only [e.apply_symm_apply] using hy

theorem reflectedTubeTransverse_frontier (closing : SignedAxisPermutation)
    (d : ℝ) (hd : 0 < d) (x : P2) :
    reflectedTubeTransverse closing d hd x ∈ frontier signedTubeDiamond ↔
      x ∈ frontier (Icc (-d) d ×ˢ Icc (-d) d) := by
  let e := reflectedTubeTransverse closing d hd
  have h := e.toHomeomorph.image_frontier (Icc (-d) d ×ˢ Icc (-d) d)
  change e '' frontier _ = frontier (e '' _) at h
  dsimp only [e] at h
  rw [reflectedTubeTransverse_image closing d hd] at h
  rw [← h]
  exact e.injective.mem_set_image

private theorem mem_square_frontier {d : ℝ} (hd : 0 < d) (x : P2) :
    x ∈ frontier (Icc (-d) d ×ˢ Icc (-d) d) ↔
      x ∈ Icc (-d) d ×ˢ Icc (-d) d ∧ (|x.1| = d ∨ |x.2| = d) := by
  rw [frontier_prod_eq, closure_Icc,
    frontier_Icc (by linarith : -d ≤ d)]
  simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff, mem_Icc, abs_eq hd.le]
  constructor
  · rintro (⟨hx, hy | hy⟩ | ⟨hx | hx, hy⟩) <;> subst_vars <;>
      constructor <;> simp_all <;> linarith
  · rintro ⟨⟨hx, hy⟩, h | h⟩
    · exact Or.inr ⟨h.symm, hy⟩
    · exact Or.inl ⟨hx, h.symm⟩

theorem reflectedTubeCoordinates_side_mem (closing : SignedAxisPermutation)
    (a b L d : ℝ) (hab : a < b) (hL : 0 < L) (hd : 0 < d) (z : C3) :
    reflectedTubeCoordinates closing a b L d hab hL hd z ∈
        frontier signedTubeDiamond ×ˢ Icc a b ↔ z ∈ singleReflectionTubeSide L d := by
  change (_ ∈ frontier signedTubeDiamond ∧ _ ∈ Icc a b) ↔ _
  rw [reflectedTubeCoordinates_time_iff]
  change (reflectedTubeTransverse closing d hd z.1 ∈ frontier signedTubeDiamond ∧ _) ↔ _
  rw [reflectedTubeTransverse_frontier, mem_square_frontier hd]
  change ((_) ∧ _) ∧ _ ↔ (_ ∧ _) ∧ _
  tauto

theorem reflectedTubeCoordinates_side_image (closing : SignedAxisPermutation)
    (a b L d : ℝ) (hab : a < b) (hL : 0 < L) (hd : 0 < d) :
    reflectedTubeCoordinates closing a b L d hab hL hd '' singleReflectionTubeSide L d =
      frontier signedTubeDiamond ×ˢ Icc a b := by
  let e := reflectedTubeCoordinates closing a b L d hab hL hd
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (reflectedTubeCoordinates_side_mem closing a b L d hab hL hd x).mpr hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (reflectedTubeCoordinates_side_mem closing a b L d hab hL hd (e.symm y)).mp
    change e (e.symm y) ∈ frontier signedTubeDiamond ×ˢ Icc a b
    simpa only [e.apply_symm_apply] using hy

theorem reflectedTubeCoordinates_endpoint_iff (closing : SignedAxisPermutation)
    (a b L d : ℝ) (hab : a < b) (hL : 0 < L) (hd : 0 < d) (z : C3) :
    ((reflectedTubeCoordinates closing a b L d hab hL hd z).2 = a ↔ z.2 = 0) ∧
      ((reflectedTubeCoordinates closing a b L d hab hL hd z).2 = b ↔ z.2 = 2 * L) := by
  rw [reflectedTubeCoordinates_apply]
  have hk : 0 < (b - a) / (2 * L) := div_pos (sub_pos.mpr hab) (by positivity)
  have hend := reflected_time_end (a := a) (b := b) hL
  constructor <;> constructor <;> intro h <;> nlinarith

theorem reflectedTubeTransverse_closing_iff (closing : SignedAxisPermutation)
    (hswap : closing.swap = true) (hsign : closing.sign 0 = closing.sign 1)
    (d : ℝ) (hd : 0 < d) (x y : P2) :
    closing.linear (reflectedTubeTransverse closing d hd x) =
        reflectedTubeTransverse closing d hd y ↔ x = (y.1, -y.2) := by
  rw [reflectedTubeTransverse_conjugate closing hswap hsign,
    (reflectedTubeTransverse closing d hd).injective.eq_iff]
  simp only [Prod.ext_iff, neg_eq_iff_eq_neg]


noncomputable def normalizedReflectedTube {E : Type*} (closing : SignedAxisPermutation)
    (a b L d : ℝ) (hab : a < b) (hL : 0 < L) (hd : 0 < d) (sigma : C3 → E) : C3 → E :=
  sigma ∘ reflectedTubeCoordinates closing a b L d hab hL hd

set_option maxHeartbeats 800000 in
theorem normalizedReflectedTube_fibers {E : Type*} (closing : SignedAxisPermutation)
    (hswap : closing.swap = true) (hsign : closing.sign 0 = closing.sign 1)
    (a b L d : ℝ) (hab : a < b) (hL : 0 < L) (hd : 0 < d) (sigma : C3 → E)
    (hfib : ∀ z ∈ signedTubeDiamond ×ˢ Icc a b,
      ∀ w ∈ signedTubeDiamond ×ˢ Icc a b,
        sigma z = sigma w ↔ z = w ∨
          (z.2 = a ∧ w.2 = b ∧ closing.linear z.1 = w.1) ∨
          (w.2 = a ∧ z.2 = b ∧ closing.linear w.1 = z.1))
    (z : C3) (hz : z ∈ singleReflectionTube L d)
    (w : C3) (hw : w ∈ singleReflectionTube L d) :
    normalizedReflectedTube closing a b L d hab hL hd sigma z =
        normalizedReflectedTube closing a b L d hab hL hd sigma w ↔
      z = w ∨ (z.1 = (w.1.1, -w.1.2) ∧
        ((z.2 = 0 ∧ w.2 = 2 * L) ∨ (z.2 = 2 * L ∧ w.2 = 0))) := by
  let e := reflectedTubeCoordinates closing a b L d hab hL hd
  change sigma (e z) = sigma (e w) ↔ _
  rw [hfib _ ((reflectedTubeCoordinates_mem closing a b L d hab hL hd z).mpr hz)
    _ ((reflectedTubeCoordinates_mem closing a b L d hab hL hd w).mpr hw),
    e.injective.eq_iff]
  have hzends := reflectedTubeCoordinates_endpoint_iff closing a b L d hab hL hd z
  have hwends := reflectedTubeCoordinates_endpoint_iff closing a b L d hab hL hd w
  have hzw := reflectedTubeTransverse_closing_iff closing hswap hsign d hd z.1 w.1
  have hwz := reflectedTubeTransverse_closing_iff closing hswap hsign d hd w.1 z.1
  change (closing.linear (e z).1 = (e w).1 ↔ _) at hzw
  change (closing.linear (e w).1 = (e z).1 ↔ _) at hwz
  rw [hzends.1, hzends.2, hwends.1, hwends.2, hzw, hwz]
  have hrev : w.1 = (z.1.1, -z.1.2) ↔ z.1 = (w.1.1, -w.1.2) := by
    simp only [Prod.ext_iff]
    constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor
    · exact h₀.symm
    · linarith
    · exact h₀.symm
    · linarith
  rw [hrev]
  tauto

theorem normalizedReflectedTube_image {E : Type*} (closing : SignedAxisPermutation)
    (a b L d : ℝ) (hab : a < b) (hL : 0 < L) (hd : 0 < d) (sigma : C3 → E) :
    normalizedReflectedTube closing a b L d hab hL hd sigma '' singleReflectionTube L d =
      sigma '' (signedTubeDiamond ×ˢ Icc a b) := by
  rw [normalizedReflectedTube, Function.comp_def,
    ← image_image sigma (reflectedTubeCoordinates closing a b L d hab hL hd),
    reflectedTubeCoordinates_image]

theorem normalizedReflectedTube_side_image {E : Type*} (closing : SignedAxisPermutation)
    (a b L d : ℝ) (hab : a < b) (hL : 0 < L) (hd : 0 < d) (sigma : C3 → E) :
    normalizedReflectedTube closing a b L d hab hL hd sigma ''
        singleReflectionTubeSide L d = sigma '' (frontier signedTubeDiamond ×ˢ Icc a b) := by
  rw [normalizedReflectedTube, Function.comp_def,
    ← image_image sigma (reflectedTubeCoordinates closing a b L d hab hL hd),
    reflectedTubeCoordinates_side_image]

theorem normalizedReflectedTube_finitePL {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (closing : SignedAxisPermutation)
    (a b L d : ℝ) (hab : a < b) (hL : 0 < L) (hd : 0 < d) (sigma : C3 → E)
    (hPL : FinitePiecewiseAffineOn sigma (signedTubeDiamond ×ˢ Icc a b)) :
    FinitePiecewiseAffineOn (normalizedReflectedTube closing a b L d hab hL hd sigma)
      (singleReflectionTube L d) := by
  let e := reflectedTubeCoordinates closing a b L d hab hL hd
  have h := hPL.precomp_affineEquiv e
  have hsource : e.symm '' (signedTubeDiamond ×ˢ Icc a b) = singleReflectionTube L d := by
    rw [← reflectedTubeCoordinates_image closing a b L d hab hL hd]
    exact e.toEquiv.symm_image_image _
  rw [hsource] at h
  exact h

theorem reflectedTubeTransverse_axis (closing : SignedAxisPermutation)
    (d : ℝ) (hd : 0 < d) (x : P2) :
    reflectedTubeTransverse closing d hd x = (0, 0) ↔ x = (0, 0) :=
  (reflectedTubeTransverse closing d hd).map_eq_zero_iff

theorem normalizedReflectedTube_polyhedralPL
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    (atlas : ι → OpenPartialHomeomorph X F) (closing : SignedAxisPermutation)
    (a b L d : ℝ) (hab : a < b) (hL : 0 < L) (hd : 0 < d) (sigma : C3 → X)
    (hPL : PolyhedralPLInCharts atlas sigma (signedTubeDiamond ×ˢ Icc a b)) :
    PolyhedralPLInCharts atlas (normalizedReflectedTube closing a b L d hab hL hd sigma)
      (singleReflectionTube L d) := by
  have hI := isFinitePLBallPair_Icc (show -d < d by linarith)
  have hbox := (hI.prod hI).prod (isFinitePLBallPair_Icc (show 0 < 2 * L by linarith))
  obtain ⟨_, _, _, _, _, c, hc, _⟩ := hbox
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hc
  change K.space = singleReflectionTube L d at hKs
  let e := reflectedTubeCoordinates closing a b L d hab hL hd
  have he : FinitePiecewiseAffineOn e K.space :=
    (K.affineOnFaces_affine e.toContinuousAffineMap).finitePiecewiseAffineOn hK
  have hm : MapsTo e K.space (signedTubeDiamond ×ˢ Icc a b) := by
    intro z hz
    exact (reflectedTubeCoordinates_mem closing a b L d hab hL hd z).mpr (hKs.subset hz)
  have hh := hPL.comp_finitePiecewiseAffineOn K hK he hm
  rw [hKs] at hh
  exact hh

theorem reflectedTubeTransverse_sheet (closing : SignedAxisPermutation)
    (d : ℝ) (hd : 0 < d) (x : P2) (hx : x ∈ Icc (-d) d ×ˢ Icc (-d) d)
    (i : Fin 2) :
    reflectedTubeTransverse closing d hd x ∈ signedTubeSheet i ↔
      x.2 = if i = 0 then x.1 else -x.1 := by
  rw [signedTubeSheet_coordinate_iff _
    ((reflectedTubeTransverse_mem closing d hd x).mpr hx)]
  fin_cases i <;> cases hs : closing.sign 0 <;>
    simp [reflectedTubeTransverse_apply, SignedAxisPermutation.reflectionCoordinates,
      SignedAxisPermutation.reflectionFrame, SignedAxisPermutation.linear_apply,
      signedSquareToDiamond_apply, hs, smul_eq_mul, hd.ne'] <;> constructor <;>
    intro h <;> nlinarith


theorem normalizedReflectedTube_old_sheets {E : Type*} (closing : SignedAxisPermutation)
    (a b L d : ℝ) (hab : a < b) (hL : 0 < L) (hd : 0 < d) (sigma : C3 → E)
    (K : Set E)
    (hK : ∀ z ∈ signedTubeDiamond ×ˢ Icc a b,
      sigma z ∈ K ↔ z.1 ∈ signedTubeSheet 0 ∪ signedTubeSheet 1)
    (z : C3) (hz : z ∈ singleReflectionTube L d) :
    normalizedReflectedTube closing a b L d hab hL hd sigma z ∈ K ↔
      z.1.2 = z.1.1 ∨ z.1.2 = -z.1.1 := by
  rw [normalizedReflectedTube, Function.comp_apply,
    hK _ ((reflectedTubeCoordinates_mem closing a b L d hab hL hd z).mpr hz)]
  change reflectedTubeTransverse closing d hd z.1 ∈ signedTubeSheet 0 ∪ signedTubeSheet 1 ↔ _
  rw [mem_union, reflectedTubeTransverse_sheet closing d hd z.1 hz.1,
    reflectedTubeTransverse_sheet closing d hd z.1 hz.1]
  norm_num

theorem normalizedReflectedTube_old_axis {E : Type*} (closing : SignedAxisPermutation)
    (a b L d : ℝ) (hab : a < b) (hL : 0 < L) (hd : 0 < d) (sigma : C3 → E)
    (K : Set E)
    (hK : ∀ z ∈ signedTubeDiamond ×ˢ Icc a b, sigma z ∈ K ↔ z.1 = (0, 0))
    (z : C3) (hz : z ∈ singleReflectionTube L d) :
    normalizedReflectedTube closing a b L d hab hL hd sigma z ∈ K ↔ z.1 = (0, 0) := by
  rw [normalizedReflectedTube, Function.comp_apply,
    hK _ ((reflectedTubeCoordinates_mem closing a b L d hab hL hd z).mpr hz)]
  exact reflectedTubeTransverse_axis closing d hd z.1

end PoincareConjecture.M76.Dehn
