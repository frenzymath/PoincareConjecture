import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusBlocks
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps











set_option autoImplicit false

open Set Geometry

namespace PLAnnularStrip





theorem finitePiecewiseAffineOn_wrappedStripMap {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) :
    FinitePiecewiseAffineOn (wrappedStripMap L) (rectangle (4 * L) d) := by
  obtain ⟨e, ⟨f, hf, he⟩, heval⟩ := exists_finitePL_strip_homeomorph hd hwidth
  have hstrip : FinitePiecewiseAffineOn (stripMap L) (rectangle L d) :=
    hf.congr fun p hp => (he ⟨p, hp⟩).symm.trans (heval ⟨p, hp⟩)
  let a (i : Fin 4) : (ℝ × ℝ) ≃ᴬ[ℝ] (ℝ × ℝ) :=
    ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ) ((i.val : ℝ) * L, 0)
  have hi (i : Fin 4) :
      FinitePiecewiseAffineOn (wrappedStripMap L) (a i '' rectangle L d) := by
    have h := (hstrip.postcomp (stripRotation L i)).precomp_affineEquiv (a i).symm
    rw [ContinuousAffineEquiv.symm_symm] at h
    apply h.congr
    rintro _ ⟨p, hp, rfl⟩
    simp only [Function.comp_apply, ContinuousAffineEquiv.symm_apply_apply]
    have ht : 4 * |p.2| < L :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr hp.2) (by norm_num)) hwidth
    change stripRotation L i (stripMap L p) =
      wrappedStripMap L ((i.val : ℝ) * L + p.1, 0 + p.2)
    simpa only [zero_add, add_zero, add_comm] using (wrappedStripMap_block ht hp.1 i).symm
  have hcover : (⋃ i, a i '' rectangle L d) = rectangle (4 * L) d := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, q, hq, rfl⟩ := mem_iUnion.mp hp
      change ((i.val : ℝ) * L + q.1 ∈ Icc 0 (4 * L)) ∧
        0 + q.2 ∈ Icc (-d) d
      refine ⟨?_, by simpa only [zero_add] using hq.2⟩
      fin_cases i <;> norm_num <;> constructor <;> linarith [hq.1.1, hq.1.2]
    · intro hp
      obtain ⟨i, s, hs, he⟩ := exists_period_block hp.1
      apply mem_iUnion.mpr
      refine ⟨i, (s, p.2), ⟨hs, hp.2⟩, ?_⟩
      change ((i.val : ℝ) * L + s, 0 + p.2) = p
      exact Prod.ext (by linarith) (zero_add _)
  rw [← hcover]
  exact FinitePiecewiseAffineOn.iUnion hi

end PLAnnularStrip
