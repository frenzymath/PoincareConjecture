import PoincareConjecture.Proofs.M38.ProjectiveCollarClock
import PoincareConjecture.Proofs.M38.ProjectivePolarBall

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem exists_projectiveBall_linear_collar_cover
    (B : SurgeryBallEmbedding projectiveCarrier.{u}) :
    ∃ q : RoundCylinderSpace → projectiveCarrier.{u}.carrier,
      IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q ∧
      (∀ x y, q x = q y ↔ x = y ∨ x = (-y.1, -y.2)) ∧
      (∀ p, q p ∈ B.closedBall ↔ 1 ≤ |p.2|) ∧
      q '' (univ ×ˢ Ioo (-1 : ℝ) 1) = B.closedBallᶜ ∧
      ∀ (z : UnitTwoSphere) (s : ℝ), |s| ≤ 1 / 16 →
        q (z, 1 - s / 2) = B.map ((1 + s) • z.val) := by
  obtain ⟨q, hq, hfibers, _, hball, himage, hradial⟩ :=
    exists_projectiveBall_cylindrical_cover B
  obtain ⟨f, hmono, hodd, hone, hformula⟩ := exists_projective_collar_clock
  let D := (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞).prodCongr f
  have hD (p : RoundCylinderSpace) : D p = (p.1, f p.2) := rfl
  have hDneg (p : RoundCylinderSpace) : D (-p.1, -p.2) = (-(D p).1, -(D p).2) := by
    change (-p.1, f (-p.2)) = (-p.1, -f p.2)
    rw [hodd]
  have hminus : f (-1) = -1 := by rw [hodd, hone]
  have habs (t : ℝ) : |f t| < 1 ↔ |t| < 1 := by
    calc
      |f t| < 1 ↔ f (-1) < f t ∧ f t < f 1 := by rw [abs_lt, hminus, hone]
      _ ↔ -1 < t ∧ t < 1 := and_congr hmono.lt_iff_lt hmono.lt_iff_lt
      _ ↔ |t| < 1 := abs_lt.symm
  have hstrip (p : RoundCylinderSpace) :
      D p ∈ univ ×ˢ Ioo (-1 : ℝ) 1 ↔ p ∈ univ ×ˢ Ioo (-1 : ℝ) 1 := by
    rw [hD]
    simpa only [mem_prod, mem_univ, true_and, mem_Ioo, ← abs_lt] using habs p.2
  refine ⟨q ∘ D, fun p => (D.isLocalDiffeomorph p).comp (𝓡 3)
    projectiveCarrier.carrier (hq _), ?_, ?_, ?_, ?_⟩
  · intro x y
    change q (D x) = q (D y) ↔ _
    rw [hfibers, ← hDneg]
    exact or_congr D.injective.eq_iff D.injective.eq_iff
  · intro p
    change q (D p) ∈ B.closedBall ↔ _
    rw [hball]
    exact not_lt.symm.trans ((not_congr (habs p.2)).trans not_lt)
  · rw [image_comp]
    have himageD : D '' (univ ×ˢ Ioo (-1 : ℝ) 1) = univ ×ˢ Ioo (-1 : ℝ) 1 := by
      apply subset_antisymm
      · rintro _ ⟨p, hp, rfl⟩
        exact (hstrip p).mpr hp
      · intro p hp
        refine ⟨D.symm p, ?_, D.apply_symm_apply p⟩
        apply (hstrip _).mp
        rwa [D.apply_symm_apply]
    rw [himageD, himage]
  · intro z s hs
    change q (z, f (1 - s / 2)) = _
    rw [hformula s hs]
    have hb := abs_le.mp hs
    exact hradial z (1 + s) (by linarith) (by linarith)

end PoincareConjecture.M38
