import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLevelChartTransport

set_option autoImplicit false

open Set

namespace Homeomorph

variable {E : Type*} [TopologicalSpace E]

theorem collar_level_mem_moved_cap_iff
    {B T d b : Set E} {upper g A : E → ℝ}
    (C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hdplane : d ⊆ {x | A x = 0}) (hcap : d ∩ T = b) (H : E ≃ₜ E)
    {t c : ℝ} (L : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)} → E)
    (hLp : ∀ x : {x : E | x ∈ B ∧ c ∈ Icc (t * g x) (upper x)},
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).1 = (x : E) ∧ L x = H (C p) ∧
      (t * g x = c ↔ (p : E × ℝ).2 = 0)) :
    ∀ x, L x ∈ H '' d ↔ (x : E) ∈ b ∧ t * g x = c := by
  intro x
  obtain ⟨p, hpbase, hpval, hplo⟩ := hLp x
  constructor
  · rintro ⟨y, hy, hyl⟩
    have hCp : (C p : E) = y := H.injective (hpval.symm.trans hyl.symm)
    have hp0 : (p : E × ℝ).2 = 0 :=
      (hheight p).symm.trans ((congrArg A hCp).trans (hdplane hy))
    have hCd : (C p : E) ∈ d := hCp.symm ▸ hy
    have hCb : (C p : E) ∈ b := hcap.subset ⟨hCd, (C p).property⟩
    have hCpx : (C p : E) = (x : E) := (hbottom p hp0).trans hpbase
    exact ⟨hCpx ▸ hCb, hplo.mpr hp0⟩
  · rintro ⟨hxb, hxlo⟩
    have hCpx : (C p : E) = (x : E) := (hbottom p (hplo.mp hxlo)).trans hpbase
    rw [hpval, hCpx]
    exact mem_image_of_mem H (hcap.symm.subset hxb).1

end Homeomorph
