import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.Support
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall

set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "p₀" => ((-1, 0) : P2)
local notation "p₁" => ((1, 0) : P2)

theorem exists_annular_terminal_strip_support
    {W : Set P2} {a b : ℝ}
    (hW : IsFinitePLBallPair ℝ W {p₀, p₁}) (hwidth : b - a < 32)
    (hstrip : W ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc a b)
    (hproper : W \ {p₀, p₁} ⊆ Ioo (-1 : ℝ) 1 ×ˢ univ) :
    ∃ S : Set P2, IsFinitePLBallPair P2 S (frontier S) ∧ S ⊆ Ann ∧
      annularLiftProjection p₀ ∈ frontier S ∧ annularLiftProjection p₁ ∈ frontier S ∧
      annularLiftProjection p₀ ≠ annularLiftProjection p₁ ∧
      IsFinitePLBallPair ℝ (annularLiftProjection '' W)
        {annularLiftProjection p₀, annularLiftProjection p₁} ∧
      IsFinitePLBallPair ℝ (annularLiftProjection '' segment ℝ p₀ p₁)
        {annularLiftProjection p₀, annularLiftProjection p₁} ∧
      (annularLiftProjection '' W) \ {annularLiftProjection p₀, annularLiftProjection p₁}
        ⊆ S \ frontier S ∧
      (annularLiftProjection '' segment ℝ p₀ p₁) \
        {annularLiftProjection p₀, annularLiftProjection p₁} ⊆ S \ frontier S ∧
      ∀ x ∈ S, depth 8 x = -1 ∨ depth 8 x = 1 → x ∈ frontier S := by
  classical
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  have hzero := (hstrip (hW.1 (show p₀ ∈ ({p₀, p₁} : Set P2) by simp))).2
  have hab : a ≤ b := hzero.1.trans hzero.2
  let eps := (32 - (b - a)) / 4
  have heps : 0 < eps := by dsimp [eps]; linarith
  let D : Set P2 := Icc (-1 : ℝ) 1 ×ˢ Icc (a - eps) (b + eps)
  have hDwidth : b + eps < a - eps + 32 := by dsimp [eps]; linarith
  have hDpair := (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1)).prod
    (isFinitePLBallPair_Icc (show a - eps < b + eps by linarith))
  have hD : IsFinitePLBallPair P2 D (frontier D) :=
    hDpair.frontier_eq_of_finrank_eq rfl ▸ hDpair
  have hDi : interior D = Ioo (-1 : ℝ) 1 ×ˢ Ioo (a - eps) (b + eps) := by
    simp only [D, interior_prod_eq, interior_Icc]
  have hWD : W ⊆ D := fun x hx =>
    ⟨(hstrip hx).1, ⟨by linarith [(hstrip hx).2.1], by linarith [(hstrip hx).2.2]⟩⟩
  have hsD : segment ℝ p₀ p₁ ⊆ D :=
    ((convex_Icc _ _).prod (convex_Icc _ _)).segment_subset
      (hWD (hW.1 (by simp))) (hWD (hW.1 (by simp)))
  have hWi : W \ {p₀, p₁} ⊆ interior D := by
    intro x hx
    rw [hDi]
    exact ⟨(hproper hx).1, ⟨by linarith [(hstrip hx.1).2.1],
      by linarith [(hstrip hx.1).2.2]⟩⟩
  have hsi : segment ℝ p₀ p₁ \ {p₀, p₁} ⊆ interior D := by
    intro x hx
    have hh := hsD hx.1
    have hxzero : x.2 = 0 := by
      have hz := ((convex_univ : Convex ℝ (univ : Set ℝ)).prod (convex_singleton (0 : ℝ))).segment_subset
        (show p₀ ∈ (univ ×ˢ ({0} : Set ℝ)) by simp)
        (show p₁ ∈ (univ ×ˢ ({0} : Set ℝ)) by simp) hx.1
      exact hz.2
    rw [hDi]
    refine ⟨⟨lt_of_le_of_ne hh.1.1 ?_, lt_of_le_of_ne hh.1.2 ?_⟩, ?_⟩
    · intro h
      exact hx.2 (Or.inl (Prod.ext h.symm hxzero))
    · intro h
      exact hx.2 (Or.inr (Prod.ext h hxzero))
    · rw [hxzero]
      constructor <;> linarith [hzero.1, hzero.2]
  have hDcopy := hD
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hDcopy
  have hswap : FinitePiecewiseAffineOn (Prod.swap : P2 → P2) D := by
    rw [← hKs]
    exact (K.affineOnFaces_affine
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousAffineEquiv.toContinuousAffineMap).finitePiecewiseAffineOn hK
  have hproj : FinitePiecewiseAffineOn annularLiftProjection D :=
    (locallyPiecewiseAffineOn_annulusMap_lift (L := 8) (d := 3 / 2)
      (by norm_num) (by norm_num) (by norm_num)).comp_finitePiecewiseAffineOn hswap (by
        intro x hx
        refine ⟨mem_univ _, ?_⟩
        change -(3 / 2 : ℝ) < x.1 ∧ x.1 < 3 / 2
        constructor <;> linarith only [hx.1.1, hx.1.2])
  have hdepth (x : P2) (hx : x ∈ D) : depth 8 (annularLiftProjection x) = x.1 := by
    exact depth_annulusMap (by norm_num) (by
      have h := abs_le.mpr hx.1
      linarith) _
  have hinj : InjOn annularLiftProjection D := by
    intro x hx y hy heq
    have h := injective_annulusMap (L := 8) (d := 1) (by norm_num) (by norm_num)
      (a₁ := ((x.2 : Circle), ⟨x.1, hx.1⟩)) (a₂ := ((y.2 : Circle), ⟨y.1, hy.1⟩)) heq
    have hh := congrArg (fun z : Circle × Icc (-1 : ℝ) 1 => (z.2 : ℝ)) h
    have hc := congrArg Prod.fst h
    exact Prod.ext hh ((AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show x.2 ∈ Ico (a - eps) (a - eps + 4 * (8 : ℝ)) from
        ⟨hx.2.1, by linarith only [hx.2.2, hDwidth]⟩)
      (show y.2 ∈ Ico (a - eps) (a - eps + 4 * (8 : ℝ)) from
        ⟨hy.2.1, by linarith only [hy.2.2, hDwidth]⟩)).mp hc)
  let S := annularLiftProjection '' D
  have hSimage := hD.image hproj hinj
  have hfront : frontier S = annularLiftProjection '' frontier D :=
    hSimage.frontier_eq_of_finrank_eq rfl
  have hS : IsFinitePLBallPair P2 S (frontier S) := hfront.symm ▸ hSimage
  have hendfront (x : P2) (hx : x ∈ D) (he : x.1 = -1 ∨ x.1 = 1) : x ∈ frontier D := by
    refine ⟨subset_closure hx, ?_⟩
    rw [hDi]
    intro hi
    rcases he with he | he <;> linarith [hi.1.1, hi.1.2]
  have hseg : IsFinitePLBallPair ℝ (segment ℝ p₀ p₁) {p₀, p₁} := by
    have h := isFinitePLBallPair_affine_interval zero_lt_one
      (ContinuousAffineMap.lineMap p₀ p₁)
      (AffineMap.lineMap_injective ℝ (show p₀ ≠ p₁ by
        intro h
        have := congrArg Prod.fst h
        norm_num at this)).injOn
    simpa only [ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one, ← segment_eq_image_lineMap] using h
  refine ⟨S, hS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact mem_squareAnnulus_iff_depth.mpr (hdepth x hx ▸ hx.1)
  · rw [hfront]
    exact mem_image_of_mem _ (hendfront p₀ (hWD (hW.1 (by simp))) (Or.inl rfl))
  · rw [hfront]
    exact mem_image_of_mem _ (hendfront p₁ (hWD (hW.1 (by simp))) (Or.inr rfl))
  · intro h
    have := hinj (hWD (hW.1 (by simp))) (hWD (hW.1 (by simp))) h
    norm_num at this
  · simpa only [image_pair] using hW.image_of_subset hproj hWD hinj
  · simpa only [image_pair] using hseg.image_of_subset hproj hsD hinj
  · rintro x ⟨⟨y, hy, rfl⟩, hn⟩
    have hyends : y ∉ ({p₀, p₁} : Set P2) := by
      rintro (rfl | rfl) <;> exact hn (by simp)
    exact (hS.interior_eq_sdiff_of_finrank_eq rfl).subset
      (hproj.mem_interior_image rfl hinj (hWi ⟨hy, hyends⟩))
  · rintro x ⟨⟨y, hy, rfl⟩, hn⟩
    have hyends : y ∉ ({p₀, p₁} : Set P2) := by
      rintro (rfl | rfl) <;> exact hn (by simp)
    exact (hS.interior_eq_sdiff_of_finrank_eq rfl).subset
      (hproj.mem_interior_image rfl hinj (hsi ⟨hy, hyends⟩))
  · rintro x ⟨y, hy, rfl⟩ he
    rw [hdepth y hy] at he
    rw [hfront]
    exact mem_image_of_mem _ (hendfront y hy he)

end PoincareConjecture.M76.Dehn
