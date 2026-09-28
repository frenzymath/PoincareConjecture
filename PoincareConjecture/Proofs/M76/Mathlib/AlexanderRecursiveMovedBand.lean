import PoincareConjecture.Proofs.M76.Mathlib.VariableHeightBand
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]





theorem IsFinitePL.exists_moved_collar_height_coordinates_with_bottom_scalar
    {B : Set E} {T : Set F} {upper bottom : E → ℝ}
    (hupper : ∀ x ∈ B, 0 ≤ upper x)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : F →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    {g : F → ℝ} (hg : FinitePiecewiseAffineOn g T)
    (hgbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → g (C p) = bottom (p : E × ℝ).1)
    (hgtop : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = upper (p : E × ℝ).1 → g (C p) = 0)
    (v : F) (hv : A.linear v = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ H : F ≃ₜ F,
      FinitePiecewiseAffineOn (H : F → F) T →
      (∀ y ∈ T, H y = y + (t * g y) • v) →
      ∃ D : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (t * bottom p.1) (upper p.1)} ≃ₜ
          (H '' T), D.IsFinitePL ∧ (∀ p, A (D p) = (p : E × ℝ).2) ∧
        (∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (t * bottom p.1) (upper p.1)},
          (p : E × ℝ).2 = upper (p : E × ℝ).1 →
          (D p : F) = C ⟨((p : E × ℝ).1, upper (p : E × ℝ).1),
            p.property.1, hupper _ p.property.1, le_rfl⟩) ∧
        ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (t * bottom p.1) (upper p.1)},
          ∃ z : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
            (z : E × ℝ).1 = (p : E × ℝ).1 ∧ (D p : F) = H (C z) ∧
              ((p : E × ℝ).2 = upper (p : E × ℝ).1 ↔
                (z : E × ℝ).2 = upper (z : E × ℝ).1) := by
  let S : Set (E × ℝ) := {p | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)}
  have hcopy := hC
  obtain ⟨f, hf, hval⟩ := hcopy
  have hmap : MapsTo f S T := by
    intro p hp
    rw [← hval ⟨p, hp⟩]
    exact (C ⟨p, hp⟩).property
  have hgf : FinitePiecewiseAffineOn (g ∘ f) S := hg.comp hf hmap
  obtain ⟨δ, hδ, hband⟩ := hgf.exists_variable_heightBand_homeomorph hupper
  refine ⟨δ, hδ, fun t ht H hH hformula => ?_⟩
  obtain ⟨K, hK, hKval⟩ := hband t ht
  let U : Set (E × ℝ) := {p | p.1 ∈ B ∧ p.2 ∈ Icc (t * bottom p.1) (upper p.1)}
  have hbot (x : E) (hx : x ∈ B) : (g ∘ f) (x, 0) = bottom x := by
    change g (f (x, 0)) = bottom x
    rw [← hval ⟨(x, 0), hx, le_rfl, hupper x hx⟩]
    exact hgbottom _ rfl
  have htop (x : E) (hx : x ∈ B) : (g ∘ f) (x, upper x) = 0 := by
    change g (f (x, upper x)) = 0
    rw [← hval ⟨(x, upper x), hx, hupper x hx, le_rfl⟩]
    exact hgtop _ rfl
  have hbandEq : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈
      Icc (0 + t * (g ∘ f) (p.1, 0))
        (upper p.1 + t * (g ∘ f) (p.1, upper p.1))} = U := by
    ext p
    constructor
    · intro hp
      have hh := hp.2
      rw [hbot p.1 hp.1, htop p.1 hp.1, mul_zero, add_zero, zero_add] at hh
      exact ⟨hp.1, hh⟩
    · intro hp
      refine ⟨hp.1, ?_⟩
      rw [hbot p.1 hp.1, htop p.1 hp.1, mul_zero, add_zero, zero_add]
      exact hp.2
  let K' : S ≃ₜ U := (Homeomorph.setCongr (rfl : S = S)).trans
    (K.trans (Homeomorph.setCongr hbandEq))
  have hK' : K'.IsFinitePL := hK.setCongr rfl hbandEq
  have hK'val (p : S) : (K' p : E × ℝ) =
      ((p : E × ℝ).1, (p : E × ℝ).2 + t * g (C p)) := by
    change (K p : E × ℝ) = _
    rw [hKval, hval p]
    rfl
  have hK'base (p : S) : (K' p : E × ℝ).1 = (p : E × ℝ).1 := by
    have h := congrArg (fun z : E × ℝ => z.1) (hK'val p)
    exact h
  have hK'roof (p : S) (hp : (p : E × ℝ).2 = upper (p : E × ℝ).1) :
      (K' p : E × ℝ) = (p : E × ℝ) := by
    rw [hK'val, hgtop p hp, mul_zero, add_zero]
  have hK'top (p : S) :
      (K' p : E × ℝ).2 = upper (K' p : E × ℝ).1 ↔
        (p : E × ℝ).2 = upper (p : E × ℝ).1 := by
    constructor
    · intro hp
      let z : S := ⟨((p : E × ℝ).1, upper (p : E × ℝ).1),
        p.property.1, hupper _ p.property.1, le_rfl⟩
      have heq : K' p = K' z := by
        apply Subtype.ext
        rw [hK'roof z rfl]
        exact Prod.ext (hK'base p) (hp.trans (congrArg upper (hK'base p)))
      exact congrArg (fun w : S => (w : E × ℝ).2) (K'.injective heq)
    · intro hp
      rw [hK'roof p hp]
      exact hp
  let D : U ≃ₜ (H '' T) := K'.symm.trans (C.trans (H.image T))
  have hD : D.IsFinitePL := hK'.symm.trans (hC.trans ⟨H, hH, fun _ => rfl⟩)
  have hbase (p : U) : (K'.symm p : E × ℝ).1 = (p : E × ℝ).1 := by
    have h := hK'base (K'.symm p)
    simpa only [K'.apply_symm_apply] using h.symm
  have hroof (p : U) : (p : E × ℝ).2 = upper (p : E × ℝ).1 ↔
      (K'.symm p : E × ℝ).2 = upper (K'.symm p : E × ℝ).1 := by
    simpa only [K'.apply_symm_apply] using hK'top (K'.symm p)
  refine ⟨D, hD, ?_, ?_, fun p => ⟨K'.symm p, hbase p, rfl, hroof p⟩⟩
  · intro p
    let z := K'.symm p
    have hpheight : (p : E × ℝ).2 = (z : E × ℝ).2 + t * g (C z) := by
      have h := congrArg Prod.snd (hK'val z)
      simpa only [z, K'.apply_symm_apply] using h
    change A (H (C z)) = (p : E × ℝ).2
    rw [hformula (C z) (C z).property, add_comm (C z : F)]
    change A ((t * g (C z)) • v +ᵥ (C z : F)) = _
    rw [A.map_vadd, map_smul, hv, hheight z, hpheight]
    change (t * g (C z)) * 1 + (z : E × ℝ).2 =
      (z : E × ℝ).2 + t * g (C z)
    ring
  · intro p hp
    let z : S := ⟨((p : E × ℝ).1, upper (p : E × ℝ).1),
      p.property.1, hupper _ p.property.1, le_rfl⟩
    have hzero : K'.symm p = z := Subtype.ext (Prod.ext (hbase p)
      (((hroof p).mp hp).trans (congrArg upper (hbase p))))
    change H (C (K'.symm p)) = C z
    rw [hzero, hformula (C z) (C z).property, hgtop z rfl,
      mul_zero, zero_smul, add_zero]

end Homeomorph
