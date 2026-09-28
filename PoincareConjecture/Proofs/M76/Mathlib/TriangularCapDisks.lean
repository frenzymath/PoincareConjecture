import PoincareConjecture.Proofs.M76.Mathlib.TriangularRoof
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLGraphs

set_option autoImplicit false

open Set Geometry

namespace TriangularRoofModel

def disk : Set ((ℝ × ℝ) × ℝ) := (fun x : ℝ × ℝ => (x, (0 : ℝ))) '' base

def rim : Set ((ℝ × ℝ) × ℝ) := (fun x : ℝ × ℝ => (x, (0 : ℝ))) '' frontier base

def cap (h : ℝ) : Set ((ℝ × ℝ) × ℝ) := (fun x => (x, h * roof x)) '' base

theorem mem_disk (p : (ℝ × ℝ) × ℝ) : p ∈ disk ↔ p.1 ∈ base ∧ p.2 = 0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hp, hz⟩
    exact ⟨p.1, hp, Prod.ext rfl hz.symm⟩

theorem mem_rim (p : (ℝ × ℝ) × ℝ) : p ∈ rim ↔ roof p.1 = 0 ∧ p.2 = 0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by simpa only [frontier_base, mem_ofPred_eq] using hx, rfl⟩
  · rintro ⟨hp, hz⟩
    exact ⟨p.1, by rwa [frontier_base], Prod.ext rfl hz.symm⟩

theorem mem_cap (h : ℝ) (p : (ℝ × ℝ) × ℝ) :
    p ∈ cap h ↔ p.1 ∈ base ∧ p.2 = h * roof p.1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hp, hz⟩
    exact ⟨p.1, hp, Prod.ext rfl hz.symm⟩

theorem isFinitePLBallPair_disk : IsFinitePLBallPair (ℝ × ℝ) disk rim := by
  let a := (ContinuousAffineMap.id ℝ (ℝ × ℝ)).prod
    (ContinuousAffineMap.const ℝ (ℝ × ℝ) (0 : ℝ))
  exact isFinitePLBallPair_base.affine_image a (fun _ _ _ _ h => congrArg Prod.fst h)

theorem isFinitePLBallPair_cap (h : ℝ) : IsFinitePLBallPair (ℝ × ℝ) (cap h) rim := by
  let a : ℝ →ᴬ[ℝ] ℝ := (h • ContinuousLinearMap.id ℝ ℝ).toContinuousAffineMap
  have hf : FinitePiecewiseAffineOn (fun x => h * roof x) base :=
    finitePiecewiseAffineOn_roof.postcomp a
  have hb : (fun x => (x, h * roof x)) '' frontier base = rim := by
    apply image_congr
    intro x hx
    have hx0 : roof x = 0 := by simpa only [frontier_base, mem_ofPred_eq] using hx
    exact Prod.ext rfl (by rw [hx0, mul_zero])
  have hpair := isFinitePLBallPair_base.graph hf
  rwa [hb] at hpair

theorem cap_inter_disk {h : ℝ} (hh : h ≠ 0) : cap h ∩ disk = rim := by
  ext p
  rw [mem_inter_iff, mem_cap, mem_disk, mem_rim]
  constructor
  · rintro ⟨⟨_, hp⟩, ⟨_, hz⟩⟩
    exact ⟨(mul_eq_zero.mp (hp.symm.trans hz)).resolve_left hh, hz⟩
  · rintro ⟨hp, hz⟩
    have hb := (roof_nonneg_iff p.1).mp hp.ge
    exact ⟨⟨hb, by rw [hz, hp, mul_zero]⟩, hb, hz⟩

theorem cap_inter_cap {h k : ℝ} (hhk : h ≠ k) : cap h ∩ cap k = rim := by
  ext p
  rw [mem_inter_iff, mem_cap, mem_cap, mem_rim]
  constructor
  · rintro ⟨⟨_, hp⟩, ⟨_, hq⟩⟩
    have heq : (h - k) * roof p.1 = 0 := by
      rw [sub_mul]
      exact sub_eq_zero.mpr (hp.symm.trans hq)
    have hz := (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr hhk)
    exact ⟨hz, by simpa only [hz, mul_zero] using hp⟩
  · rintro ⟨hp, hz⟩
    have hb := (roof_nonneg_iff p.1).mp hp.ge
    exact ⟨⟨hb, by rw [hz, hp, mul_zero]⟩, hb, by rw [hz, hp, mul_zero]⟩

end TriangularRoofModel
