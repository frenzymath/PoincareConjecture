import PoincareConjecture.Proofs.M76.Rigidity.OriginalCollarShellMap

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V3) 1
local notation "Q0" => sphere (0 : V3) (7 / 8)
local notation "J" => Icc (0 : ℝ) (1 / 8)
local notation "I" => Icc (0 : ℝ) 1
local notation "T" => (norm : V3 → ℝ) ⁻¹' Icc (7 / 8) 1

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] {K : Set X}

theorem original_collar_shell_boundary
    (L : SimplicialComplex ℝ E) (c : E × ℝ → X)
    (hi : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (E × ℝ)) => c z))
    (hproper : ∀ z : (L.space ×ˢ I : Set (E × ℝ)),
      c z ∈ frontier K ↔ (z : E × ℝ).2 = 0)
    (qH : Q ≃ₜ L.space) (h : (Q ×ˢ J : Set (V3 × ℝ)) ≃ₜ T)
    (hnorm : ∀ z : (Q ×ˢ J : Set (V3 × ℝ)),
      ‖(h z : V3)‖ = 1 - (z : V3 × ℝ).2)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (f : V3 → X)
    (hvalue : ∀ z : (Q ×ˢ J : Set (V3 × ℝ)),
      f (h z) = c ((qH ⟨(z : V3 × ℝ).1, z.property.1⟩ : E),
        8 * ε * (z : V3 × ℝ).2)) :
    (∀ x ∈ T, f x ∈ c '' (L.space ×ˢ {ε}) ↔ x ∈ Q0) ∧
      ∀ x ∈ T, f x ∈ frontier K ↔ x ∈ Q := by
  have hscale : 0 < 8 * ε := by positivity
  let A (z : (Q ×ˢ J : Set (V3 × ℝ))) : E × ℝ :=
    ((qH ⟨(z : V3 × ℝ).1, z.property.1⟩ : E), 8 * ε * (z : V3 × ℝ).2)
  have hA (z : (Q ×ˢ J : Set (V3 × ℝ))) : A z ∈ L.space ×ˢ I := by
    refine ⟨(qH ⟨(z : V3 × ℝ).1, z.property.1⟩).property,
      mul_nonneg hscale.le z.property.2.1, ?_⟩
    have hb : 8 * ε * (z : V3 × ℝ).2 ≤ ε := by nlinarith [z.property.2.2]
    exact hb.trans hε1
  have hlevel (z : (Q ×ˢ J : Set (V3 × ℝ))) :
      f (h z) ∈ c '' (L.space ×ˢ {ε}) ↔ (z : V3 × ℝ).2 = 1 / 8 := by
    rw [hvalue]
    constructor
    · rintro ⟨w, hw, hweq⟩
      have hwtime : w.2 = ε := mem_singleton_iff.mp hw.2
      have hwI : w ∈ L.space ×ˢ I := by
        refine ⟨hw.1, ?_⟩
        rw [hwtime]
        exact ⟨hε.le, hε1⟩
      have heq := hi.injective (a₁ := ⟨w, hwI⟩) (a₂ := ⟨A z, hA z⟩) hweq
      have htime : w.2 = 8 * ε * (z : V3 × ℝ).2 :=
        congrArg (fun v : (L.space ×ˢ I : Set (E × ℝ)) => v.1.2) heq
      apply mul_left_cancel₀ hscale.ne'
      rw [← htime, hwtime]
      ring
    · intro ht
      refine ⟨A z, ⟨(hA z).1, ?_⟩, rfl⟩
      change 8 * ε * (z : V3 × ℝ).2 = ε
      rw [ht]
      ring
  have hfront (z : (Q ×ˢ J : Set (V3 × ℝ))) :
      f (h z) ∈ frontier K ↔ (z : V3 × ℝ).2 = 0 := by
    rw [hvalue]
    apply (hproper ⟨A z, hA z⟩).trans
    constructor
    · exact fun ht => (mul_eq_zero.mp ht).resolve_left hscale.ne'
    · intro ht
      change 8 * ε * (z : V3 × ℝ).2 = 0
      rw [ht, mul_zero]
  have hinner (z : (Q ×ˢ J : Set (V3 × ℝ))) :
      (z : V3 × ℝ).2 = 1 / 8 ↔ (h z : V3) ∈ Q0 := by
    rw [mem_sphere_zero_iff_norm, hnorm]
    constructor <;> intro hz <;> linarith
  have houter (z : (Q ×ˢ J : Set (V3 × ℝ))) :
      (z : V3 × ℝ).2 = 0 ↔ (h z : V3) ∈ Q := by
    rw [mem_sphere_zero_iff_norm, hnorm]
    constructor <;> intro hz <;> linarith
  constructor
  · intro x hx
    have hiff := (hlevel (h.symm ⟨x, hx⟩)).trans (hinner (h.symm ⟨x, hx⟩))
    simpa only [h.apply_symm_apply] using hiff
  · intro x hx
    have hiff := (hfront (h.symm ⟨x, hx⟩)).trans (houter (h.symm ⟨x, hx⟩))
    simpa only [h.apply_symm_apply] using hiff

end PoincareConjecture.M76
