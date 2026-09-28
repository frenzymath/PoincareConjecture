import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.CircleCollarRetainedDisks












set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76
open PoincareConjecture.M76.Dehn
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "Sphere" => sphere (0 : V3) 1




theorem ChartwisePLSphere.circle_surgery_contact_ledger
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    (s : ChartwisePLSphere e S) {β : ℝ}
    (φ : P2 → V3) (k : Bool → Set V3)
    (hφS : MapsTo φ (Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) Sphere)
    (hkS : ∀ b, k b ⊆ Sphere)
    (hkaxis : ∀ b, Disjoint (k b) ((fun t : ℝ => φ (0, t)) '' Icc 0 β))
    (hwhole : (k true ∪ k false) ∪
      (φ '' (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β)) = Sphere)
    (τ : C3 → X)
    (hvalue : ∀ z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β,
      s.map (φ z) = τ ((z.1, 0), z.2))
    (T L : Set X)
    (hface : ∀ z ∈ signedTubeDiamond ×ˢ Icc 0 β, τ z ∈ T ↔ z.1.1 = 0)
    (haxis : (fun t : ℝ => τ ((0, 0), t)) '' Icc 0 β = L)
    (caps : Bool → Set X) (hcaps : ∀ b, Disjoint (caps b) T) :
    let B := (fun z : P2 => τ ((z.1, 0), z.2)) ''
      (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β)
    let new := fun b => s.map '' k b ∪ caps b
    B ∩ T = L ∧
      Disjoint (s.map '' k true ∪ s.map '' k false) L ∧
      (new true ∪ new false) ∩ T = (S ∩ T) \ L ∧
      ∀ O : Set X, B ⊆ O → (∀ b, caps b ⊆ O) →
        (new true ∪ new false) \ O = S \ O ∧
        ∀ A : Set X, Disjoint A O → (new true ∪ new false) ∩ A = S ∩ A := by
  classical
  dsimp only
  let B := (fun z : P2 => τ ((z.1, 0), z.2)) ''
    (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β)
  let R := s.map '' k true ∪ s.map '' k false
  have hquarter {z : P2} (hz : z ∈ Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β) :
      z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β :=
    ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hstrip {z : P2} (hz : z ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β) :
      ((z.1, 0), z.2) ∈ signedTubeDiamond ×ˢ Icc 0 β := by
    simpa only [signedSheetStripMap_apply, Fin.reduceEq, if_false] using
      signedSheetStripMap_mem (1 : Fin 2) hz
  have hmapSphere : s.map '' Sphere = S := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [s.map_eq ⟨x, hx⟩]
      exact (s.parametrization ⟨x, hx⟩).property
    · intro x hx
      obtain ⟨z, hz⟩ := s.parametrization.surjective ⟨x, hx⟩
      exact ⟨z, z.property, (s.map_eq z).trans (congrArg Subtype.val hz)⟩
  have hmapinj : InjOn s.map Sphere := by
    intro x hx y hy hxy
    rw [s.map_eq ⟨x, hx⟩, s.map_eq ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val (s.parametrization.injective (Subtype.ext hxy))
  have hband : s.map '' (φ '' (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ Icc 0 β)) = B := by
    rw [image_image]
    exact image_congr (fun z hz => hvalue z (hquarter hz))
  have hS : R ∪ B = S := by
    rw [← hmapSphere, ← hwhole, image_union, image_union, hband]
  have hBT : B ∩ T = L := by
    rw [← haxis]
    apply Subset.antisymm
    · rintro x ⟨⟨z, hz, hzx⟩, hxT⟩
      have hzero : z.1 = 0 := (hface _ (hstrip (hquarter hz))).mp
        (by simpa only [hzx] using hxT)
      refine ⟨z.2, hz.2, ?_⟩
      simpa only [hzero] using hzx
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨⟨(0, t), ⟨by norm_num, ht⟩, rfl⟩,
        (hface _ (hstrip (show (0, t) ∈ Icc (-1 : ℝ) 1 ×ˢ Icc 0 β from
          ⟨by norm_num, ht⟩))).mpr rfl⟩
  have hRaxis (b : Bool) : Disjoint (s.map '' k b) L := by
    rw [← haxis]
    apply Set.disjoint_left.mpr
    rintro x ⟨y, hy, hyx⟩ ⟨t, ht, htx⟩
    have heq : s.map y = s.map (φ (0, t)) :=
      hyx.trans (htx.symm.trans (hvalue (0, t) ⟨by norm_num, ht⟩).symm)
    have hyphi : y = φ (0, t) := hmapinj (hkS b hy) (hφS ⟨by norm_num, ht⟩) heq
    exact Set.disjoint_left.mp (hkaxis b) hy ⟨t, ht, hyphi.symm⟩
  have hRL : Disjoint R L := by
    exact disjoint_union_left.mpr ⟨hRaxis true, hRaxis false⟩
  have hnewT : ((s.map '' k true ∪ caps true) ∪ (s.map '' k false ∪ caps false)) ∩ T =
      R ∩ T := by
    ext x
    have ht := fun hx : x ∈ caps true => Set.disjoint_left.mp (hcaps true) hx
    have hf := fun hx : x ∈ caps false => Set.disjoint_left.mp (hcaps false) hx
    simp only [R, mem_inter_iff, mem_union]
    tauto
  refine ⟨hBT, hRL, ?_, ?_⟩
  · rw [hnewT]
    ext x
    have hSx : x ∈ S ↔ x ∈ R ∨ x ∈ B := by rw [← hS]; rfl
    have hLx : x ∈ L ↔ x ∈ B ∧ x ∈ T := by rw [← hBT]; rfl
    have hnot := fun hx : x ∈ R => Set.disjoint_left.mp hRL hx
    simp only [mem_inter_iff, mem_sdiff]
    tauto
  · intro O hBO hcapO
    have hexterior : ((s.map '' k true ∪ caps true) ∪ (s.map '' k false ∪ caps false)) \ O =
        S \ O := by
      ext x
      have hSx : x ∈ S ↔ x ∈ R ∨ x ∈ B := by rw [← hS]; rfl
      have hB := @hBO x
      have ht : x ∈ caps true → x ∈ O := fun hx => hcapO true hx
      have hf : x ∈ caps false → x ∈ O := fun hx => hcapO false hx
      simp only [R, mem_sdiff, mem_union] at hSx ⊢
      tauto
    refine ⟨hexterior, ?_⟩
    intro A hAO
    ext x
    have hn := fun hx : x ∈ A => Set.disjoint_left.mp hAO hx
    have hx := Set.ext_iff.mp hexterior x
    simp only [mem_sdiff] at hx
    simp only [mem_inter_iff]
    tauto

end PoincareConjecture.M76
