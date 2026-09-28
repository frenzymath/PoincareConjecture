import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Disks.CircleCapAttachment
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior

set_option autoImplicit false
open Set Geometry PLAnnularStrip
namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn
local notation "P2" => (ℝ × ℝ)

private noncomputable def outsideCircleStrip (β : ℝ) (positive : Bool) : P2 →ᴬ[ℝ] P2 :=
  let x : P2 →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ P2 (1 / 4) -
    ((1 / 4 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  (if positive then -x else x).prod
    ((β / 32) • ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap

private theorem outsideCircleStrip_apply (β : ℝ) (positive : Bool) (z : P2) :
    outsideCircleStrip β positive z =
      (if positive then -(1 - z.2) / 4 else (1 - z.2) / 4, β / 32 * z.1) := by
  cases positive <;> ext <;> simp [outsideCircleStrip] <;> ring

theorem exists_outer_disk_of_planar_circle_strip
    {n : ℕ} (P : Polygon P2 (n + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P) {D : Set P2}
    (hD : IsFinitePLBallPair P2 D (P.boundary ℝ))
    {β : ℝ} (hβ : 0 < β) (f : P2 → P2)
    (hf : FinitePiecewiseAffineOn f (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β))
    (hfib : ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β,
      ∀ y ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β,
      f x = f y ↔ x.1 = y.1 ∧
        (x.2 = y.2 ∨ (x.2 = 0 ∧ y.2 = β) ∨ (y.2 = 0 ∧ x.2 = β)))
    (haxis : ∀ x ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β,
      f x ∈ P.boundary ℝ ↔ x.1 = 0)
    (haxisImage : (fun t : ℝ => f (0, t)) '' Icc 0 β = P.boundary ℝ) :
    ∃ (positive : Bool) (Dout rimout : Set P2),
      IsFinitePLBallPair P2 Dout rimout ∧ D ⊆ interior Dout ∧
      Dout ⊆ D ∪ f '' (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) ∧
      rimout = (fun t => f (if positive then -1 / 2 else 1 / 2, t)) '' Icc 0 β := by
  classical
  obtain ⟨positive, _, hout, _⟩ :=
    exists_inner_disk_of_planar_circle_strip P hP hPi hD hβ f hf hfib haxis
  let C := outsideCircleStrip β positive
  have hC : ∀ z, C z =
      (if positive then -(1 - z.2) / 4 else (1 - z.2) / 4, β / 32 * z.1) :=
    outsideCircleStrip_apply β positive
  have hCmap : MapsTo C (Icc 0 (4 * 8) ×ˢ Icc (-1 : ℝ) 1)
      (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) := by
    rintro ⟨s, u⟩ ⟨hs, hu⟩
    rw [hC]
    refine ⟨?_, mul_nonneg (by positivity) hs.1, ?_⟩
    · cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals constructor <;> linarith [hu.1, hu.2]
    · nlinarith [hs.2]
  have hbox := (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 4 * 8)).prod
    (isFinitePLBallPair_Icc (by norm_num : (-1 : ℝ) < 1))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hbox
  have hCPL : FinitePiecewiseAffineOn C (Icc 0 (4 * 8) ×ˢ Icc (-1 : ℝ) 1) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine C⟩
  have hCf := hf.comp hCPL hCmap
  have hCfibs : ∀ x ∈ Icc 0 (4 * 8) ×ˢ Icc (-1 : ℝ) 1,
      ∀ y ∈ Icc 0 (4 * 8) ×ˢ Icc (-1 : ℝ) 1,
      (f ∘ C) x = (f ∘ C) y ↔ x.2 = y.2 ∧
        (x.1 : AddCircle (4 * 8 : ℝ)) = (y.1 : AddCircle (4 * 8 : ℝ)) := by
    intro x hx y hy
    let : Fact (0 < (4 * 8 : ℝ)) := ⟨by norm_num⟩
    have hfirst : (C x).1 = (C y).1 ↔ x.2 = y.2 := by
      rw [hC, hC]
      cases positive <;> simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals constructor <;> intro h <;> linarith
    have ht (s t : ℝ) : β / 32 * s = β / 32 * t ↔ s = t :=
      mul_right_inj' (by positivity)
    have hz (s : ℝ) : β / 32 * s = 0 ↔ s = 0 := by
      simpa only [mul_zero] using ht s 0
    have hend (s : ℝ) : β / 32 * s = β ↔ s = 4 * 8 := by
      have hv : β / 32 * (4 * 8) = β := by ring
      simpa only [hv] using ht s (4 * 8)
    rw [Function.comp_apply, Function.comp_apply, hfib _ (hCmap hx) _ (hCmap hy),
      hfirst, AddCircle.coe_eq_coe_iff_eq_or_endpoints hx.1 hy.1]
    simp only [hC, ht, hz, hend]
    tauto
  obtain ⟨c, hc, _, hperiod, _⟩ := _root_.Dehn.exists_finitePL_annulus_of_periodic_strip
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (4 : ℝ) * 1 < 8)
    (f ∘ C) hCf hCfibs
  let B := (f ∘ C) '' (Icc 0 (4 * 8) ×ˢ Icc (-1 : ℝ) 1)
  let q := (fun t => f (if positive then -1 / 2 else 1 / 2, t)) '' Icc 0 β
  have htime (a : ℝ) :
      (fun s : ℝ => f (a, β / 32 * s)) '' Icc 0 (4 * 8) =
        (fun t : ℝ => f (a, t)) '' Icc 0 β := by
    apply Subset.antisymm
    · rintro _ ⟨s, hs, rfl⟩
      exact ⟨β / 32 * s, ⟨mul_nonneg (by positivity) hs.1, by nlinarith [hs.2]⟩, rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      refine ⟨32 * (t / β), ⟨mul_nonneg (by norm_num) (div_nonneg ht.1 hβ.le), ?_⟩, ?_⟩
      · have := (div_le_one hβ).mpr ht.2
        nlinarith
      · ext <;> simp <;> field_simp
  have hinner : (fun s => (f ∘ C) (s, 1)) '' Icc 0 (4 * 8) = P.boundary ℝ := by
    have hv (s : ℝ) : C (s, 1) = (0, β / 32 * s) := by
      rw [hC]; cases positive <;> norm_num
    simpa only [Function.comp_apply, hv] using (htime 0).trans haxisImage
  have houter : (fun s => (f ∘ C) (s, -1)) '' Icc 0 (4 * 8) = q := by
    have hv (s : ℝ) : C (s, -1) =
        (if positive then -1 / 2 else 1 / 2, β / 32 * s) := by
      rw [hC]; cases positive <;> norm_num
    simpa only [Function.comp_apply, hv] using htime (if positive then -1 / 2 else 1 / 2)
  have hDB : D ∩ B = P.boundary ℝ := by
    apply Subset.antisymm
    · rintro _ ⟨hxD, ⟨⟨s, u⟩, ⟨hs, hu⟩, rfl⟩⟩
      have ht : β / 32 * s ∈ Icc 0 β := (hCmap ⟨hs, hu⟩).2
      by_cases hu1 : u = 1
      · subst u
        apply (haxis _ (hCmap ⟨hs, hu⟩)).mpr
        rw [hC]; cases positive <;> norm_num
      · have hpos : (1 - u) / 4 ∈ Ioc (0 : ℝ) 1 := by
          have huLt : u < 1 := lt_of_le_of_ne hu.2 hu1
          constructor <;> linarith [hu.1, huLt]
        have hn := hout ((1 - u) / 4) hpos (β / 32 * s) ht
        apply False.elim
        apply hn
        simpa only [Function.comp_apply, hC, neg_div] using hxD
    · intro x hx
      refine ⟨hD.1 hx, ?_⟩
      obtain ⟨s, hs, hsx⟩ := hinner.symm.subset hx
      exact ⟨(s, 1), ⟨hs, by norm_num⟩, hsx⟩
  have hqD : Disjoint q D := by
    apply disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩ hx
    have hn : f (if positive then -1 / 2 else 1 / 2, t) ∉ D := by
      simpa only [neg_div] using hout (1 / 2) (by norm_num) t ht
    exact hn hx
  have hball : IsFinitePLBallPair P2 (D ∪ B) q :=
    attach_periodic_annulus hD hDB c hc (f ∘ C) hperiod hinner houter
  refine ⟨positive, D ∪ B, q, hball, ?_, ?_, rfl⟩
  · rw [hball.interior_eq_sdiff_of_finrank_eq rfl]
    exact fun x hx => ⟨Or.inl hx, disjoint_right.mp hqD hx⟩
  · apply union_subset_union_right
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨C z, hCmap hz, rfl⟩

end PoincareConjecture.M76
