import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.MovedLowerEndReplacement
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.UpperEnd
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CapHeightCompression
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold Topology InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_target_three_end_replacement
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D)
    (hnonnested : Disjoint (W.disc 0).closedRegion (W.disc 1).closedRegion)
    (P : SurgeryCapProfile) (m v tau : ℝ)
    (hm : W.level < m)
    (hmc : m < ⟪(u : E3), psi (D.point, 0)⟫_ℝ)
    (hcv : ⟪(u : E3), psi (D.point, 0)⟫_ℝ < v)
    (hseams : ∀ i : Fin D.capCount, (D.cap i).sign = -1 →
      v < (D.cap i).cutHeight + (D.cap i).sign * (D.cap i).removal)
    (hlevel : IsConnected
      {q : UnitTwoSphere | ⟪(u : E3), psi (q, 0)⟫_ℝ = v})
    (htau : 0 < tau) :
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let c := H (psi (D.point, 0))
    let S : Set E3 := range (fun q : UnitTwoSphere => psi (q, 0))
    let cut : Fin 3 → ℝ := ![m, m, v]
    let sign : Fin 3 → ℝ := ![1, 1, -1]
    let R : Set E3 := S ∩ {y | m ≤ H y ∧ H y ≤ v}
    ∃ (b : ℝ) (T : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3)
      (V : Fin 2 → Set E3),
      0 < b ∧ 4 * b < tau ∧ 4 * b < c - m ∧ 4 * b < v - c ∧
      (∀ i : Fin 3,
        closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T i).source ∧
        ContDiffOn ℝ ∞ (T i) (T i).source ∧
        ContDiffOn ℝ ∞ (T i).symm (T i).target ∧
        (∀ x ∈ (T i).source, H (T i x) = x.2) ∧
        (∀ y ∈ (T i).target, ((T i).symm y).2 = H y)) ∧
      (∀ i : Fin 2, IsOpen (V i) ∧
        T i.castSucc '' (closedBall (0 : E2) 1 ×ˢ Icc (m - 4 * b) (m + 4 * b)) ⊆ V i) ∧
      Disjoint (V 0) (V 1) ∧
      (∀ z ∈ Icc (m - 4 * b) (m + 4 * b),
        S ∩ {y : E3 | H y = z} =
          ⋃ i : Fin 2, T i.castSucc '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ))) ∧
      (∀ z ∈ Icc (v - 4 * b) (v + 4 * b),
        T 2 '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
          S ∩ {y : E3 | H y = z}) ∧
      ∀ lambda : ℝ, 0 < lambda → lambda * P.heightBound < b →
        let south : Fin 3 → Set E3 := fun i =>
          P.capMap (T i) (cut i) (sign i) 0 lambda ''
            {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
        ∃ G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
          G '' S = R ∪ (⋃ i : Fin 3, south i) ∧
          G.symm '' (R ∪ (⋃ i : Fin 3, south i)) = S ∧
          (∀ (i : Fin 3) (y : E3), y ∈ south i →
            |H y - cut i| ≤ lambda * P.heightBound ∧ |H y - cut i| < tau) ∧
          IsCollarEmbedding (fun q => G (psi q)) := by
  classical
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let c := H (psi (D.point, 0))
  let S : Set E3 := range (fun q : UnitTwoSphere => psi (q, 0))
  let cut : Fin 3 → ℝ := ![m, m, v]
  let sign : Fin 3 → ℝ := ![1, 1, -1]
  let R : Set E3 := S ∩ {y | m ≤ H y ∧ H y ≤ v}
  let Rlower : Set E3 := S ∩ {y | m ≤ H y}
  let Rupper : Set E3 := S ∩ {y | H y ≤ v}
  let Eupper : Set E3 := S ∩ {y | v ≤ H y}
  change m < c at hmc
  change c < v at hcv
  obtain ⟨bL, TL, V, hbL, _hbLtau, hbLc, hTL, hVdis, hCircleL, hLaterL⟩ :=
    exists_saddle_moved_lower_end_replacement hP psi hpsi u D W hnonnested
      P m tau hm hmc htau
  choose hLs hLt hLi hLh hLhi hVopen hVstack using hTL
  obtain ⟨iU, gamma, TU, _hSign, _hUnique, hgamma, hgap,
      hUs, hUt, hUi, hUh, hUih, _hCap, _hEnd, hCircleU, hLaterU⟩ :=
    exists_saddle_upper_end_with_later_scales psi hpsi u D v hcv hseams hlevel
  let b := min bL (min gamma (min tau (v - c))) / 8
  have hmin : 0 < min bL (min gamma (min tau (v - c))) :=
    lt_min hbL (lt_min hgamma (lt_min htau (sub_pos.mpr hcv)))
  have hb : 0 < b := div_pos hmin (by norm_num)
  have hbLow : 4 * b < bL := by
    have := min_le_left bL (min gamma (min tau (v - c)))
    dsimp [b]
    linarith
  have hbGamma : 4 * b < gamma := by
    have := (min_le_right bL (min gamma (min tau (v - c)))).trans
      (min_le_left gamma (min tau (v - c)))
    dsimp [b]
    linarith
  have hbTau : 4 * b < tau := by
    have := ((min_le_right bL (min gamma (min tau (v - c)))).trans
      (min_le_right gamma (min tau (v - c)))).trans (min_le_left tau (v - c))
    dsimp [b]
    linarith
  have hbUpper : 4 * b < v - c := by
    have := ((min_le_right bL (min gamma (min tau (v - c)))).trans
      (min_le_right gamma (min tau (v - c)))).trans (min_le_right tau (v - c))
    dsimp [b]
    linarith
  have hbLower : 4 * b < c - m := by
    change 4 * bL < c - m at hbLc
    linarith
  let T : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3 := ![TL 0, TL 1, TU]
  have hTlow (i : Fin 2) : T i.castSucc = TL i := by fin_cases i <;> rfl
  have hTube (i : Fin 3) :
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T i).source ∧
      ContDiffOn ℝ ∞ (T i) (T i).source ∧
      ContDiffOn ℝ ∞ (T i).symm (T i).target ∧
      (∀ x ∈ (T i).source, H (T i x) = x.2) ∧
      (∀ y ∈ (T i).target, ((T i).symm y).2 = H y) := by
    fin_cases i
    · exact ⟨hLs 0, hLt 0, hLi 0, hLh 0, hLhi 0⟩
    · exact ⟨hLs 1, hLt 1, hLi 1, hLh 1, hLhi 1⟩
    · exact ⟨hUs, hUt, hUi, hUh, hUih⟩
  have hLowerWindow : Icc (m - 4 * b) (m + 4 * b) ⊆
      Icc (m - 4 * bL) (m + 4 * bL) := by
    intro z hz
    constructor <;> linarith [hz.1, hz.2]
  refine ⟨b, T, V, hb, hbTau, hbLower, hbUpper, hTube, ?_, hVdis, ?_, ?_, ?_⟩
  · intro i
    refine ⟨hVopen i, ?_⟩
    rw [hTlow]
    exact (image_mono (prod_mono_right hLowerWindow)).trans (hVstack i)
  · intro z hz
    rw [hCircleL z (hLowerWindow hz)]
    exact iUnion_congr (fun i => by rw [hTlow])
  · intro z hz
    change TU '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) = S ∩ {y | H y = z}
    apply hCircleU
    constructor <;> linarith [hz.1, hz.2]
  intro lambda hlambda hsmall
  let south : Fin 3 → Set E3 := fun i =>
    P.capMap (T i) (cut i) (sign i) 0 lambda ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  obtain ⟨Glow, hLowImage, _hLowInv, _hLowHeights, _hLowCollar⟩ :=
    hLaterL (fun _ => lambda) (fun _ => hlambda) (fun _ => hsmall.trans (by linarith))
  change Glow '' S = Rlower ∪ south 0 ∪ south 1 at hLowImage
  have hCapHeights (i : Fin 3) (y : E3) (hy : y ∈ south i) :
      |H y - cut i| ≤ lambda * P.heightBound := by
    obtain ⟨q, _hq, rfl⟩ := hy
    have hs : ((P.model q).1, cut i + sign i * (0 + lambda * (P.model q).2)) ∈
        (T i).source :=
      (hTube i).1 ⟨mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q), mem_univ _⟩
    rw [SurgeryCapProfile.capMap_apply, (hTube i).2.2.2.1 _ hs]
    have hsign : |sign i| = 1 := by fin_cases i <;> norm_num [sign]
    simp only [zero_add, add_sub_cancel_left, abs_mul, hsign, one_mul, abs_of_pos hlambda]
    exact mul_le_mul_of_nonneg_left (P.height_bound q) hlambda.le
  have hBelow (i : Fin 2) (y : E3) (hy : y ∈ south i.castSucc) : H y ≤ c := by
    have hh := (abs_le.mp (hCapHeights i.castSucc y hy)).2
    have hc : cut i.castSucc = m := by fin_cases i <;> rfl
    rw [hc] at hh
    linarith
  obtain ⟨_Au, _Nu, Gup, _Ku, _hAb, _hNb, _hNs, _hNt, _hNp, _hNi,
      _hSlices, _hAlower, _hContain, _hShort, _hShared, _hRim, _hAvoid, _hRet,
      hUpperImage, _hUpperInv, hFix, _hK, _hKsub, _hKabove, _hKs, _hKis,
      _hUpperS, _hUpperSi⟩ :=
    hLaterU P lambda tau c hlambda (hsmall.trans (by linarith))
      (hsmall.trans (by linarith)) (hsmall.trans (by linarith))
  have hUpperCap :
      (fun q : UnitTwoSphere => TU ((P.model q).1, v - lambda * (P.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} = south 2 := by
    apply image_congr
    intro q _
    change TU ((P.model q).1, v - lambda * (P.model q).2) =
      TU ((P.model q).1, v + (-1) * (0 + lambda * (P.model q).2))
    apply congrArg TU
    apply Prod.ext
    · rfl
    · ring
  change Gup '' Eupper =
    (fun q : UnitTwoSphere => TU ((P.model q).1, v - lambda * (P.model q).2)) ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} at hUpperImage
  rw [hUpperCap] at hUpperImage
  have hSplit : Rlower = R ∪ Eupper := by
    ext y
    constructor
    · rintro ⟨hyS, hym⟩
      by_cases hyv : H y ≤ v
      · exact Or.inl ⟨hyS, hym, hyv⟩
      · exact Or.inr ⟨hyS, (lt_of_not_ge hyv).le⟩
    · rintro (⟨hyS, hym, _⟩ | ⟨hyS, hyv⟩)
      · exact ⟨hyS, hym⟩
      · exact ⟨hyS, (hmc.trans hcv).le.trans hyv⟩
  have hFixR (y : E3) (hy : y ∈ R) : Gup y = y := by
    exact (hFix y (Or.inl (Or.inr ⟨hy.1, hy.2.2⟩))).1
  have hFixLower (i : Fin 2) (y : E3) (hy : y ∈ south i.castSucc) : Gup y = y :=
    (hFix y (Or.inr (hBelow i y hy))).1
  have hFixedImage (X : Set E3) (hX : ∀ y ∈ X, Gup y = y) : Gup '' X = X := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [hX x hx] using hx
    · intro hy
      exact ⟨y, hy, hX y hy⟩
  have hGR : Gup '' R = R := hFixedImage R hFixR
  have hG0 : Gup '' south 0 = south 0 := hFixedImage _ (hFixLower 0)
  have hG1 : Gup '' south 1 = south 1 := hFixedImage _ (hFixLower 1)
  have hUnion3 (X : Fin 3 → Set E3) : (⋃ i, X i) = X 0 ∪ X 1 ∪ X 2 := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((hy | hy) | hy)
      · exact mem_iUnion.mpr ⟨0, hy⟩
      · exact mem_iUnion.mpr ⟨1, hy⟩
      · exact mem_iUnion.mpr ⟨2, hy⟩
  let G := Glow.trans Gup
  have hImage : G '' S = R ∪ (⋃ i : Fin 3, south i) := by
    calc
      _ = Gup '' (Glow '' S) := by rw [image_image]; rfl
      _ = R ∪ south 2 ∪ south 0 ∪ south 1 := by
        rw [hLowImage, hSplit, image_union, image_union, image_union,
          hGR, hUpperImage, hG0, hG1]
      _ = _ := by rw [hUnion3]; ac_rfl
  refine ⟨G, hImage, ?_, ?_, IsCollarEmbedding.postcompose_diffeomorph hpsi G⟩
  · rw [← hImage]
    exact G.symm_image_image S
  · intro i y hy
    exact ⟨hCapHeights i y hy, (hCapHeights i y hy).trans_lt
      (hsmall.trans (by linarith))⟩

end PoincareConjecture.M25.Topology3D
