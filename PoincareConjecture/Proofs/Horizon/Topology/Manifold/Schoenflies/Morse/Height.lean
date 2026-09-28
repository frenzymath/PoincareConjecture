import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Normal
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularValues










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem mfderiv_height_apply
    {f : S2 -> E3} (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f)
    (v : E3) (p : S2) (u : TangentSpace (𝓡 2) p) :
    mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p u =
      inner Real v (mfderiv (𝓡 2) (𝓡 3) f p u) := by
  have h := mfderiv_comp p
    (((innerSL Real v).contMDiff (n := ∞)).contMDiffAt.mdifferentiableAt (by simp))
    ((hf p).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at h
  exact congrArg (fun A : TangentSpace (𝓡 2) p →L[Real] Real => A u) h

private theorem eq_or_eq_neg_of_smul (v w : S2) {c : Real}
    (hc : (v : E3) = c • (w : E3)) : v = w ∨ v = -w := by
  have hn := congrArg norm hc
  have hcabs : |c| = 1 := by simpa only [norm_eq_of_mem_sphere, norm_smul,
    Real.norm_eq_abs, mul_one] using hn.symm
  rcases le_total 0 c with hpos | hneg
  · have heq : c = 1 := by simpa only [abs_of_nonneg hpos] using hcabs
    left
    apply Subtype.ext
    simpa only [heq, one_smul] using hc
  · have heq : c = -1 := by rw [abs_of_nonpos hneg] at hcabs; linarith
    right
    apply Subtype.ext
    change (v : E3) = -(w : E3)
    simpa only [heq, neg_one_smul] using hc

theorem height_critical_iff_normal
    {f : S2 -> E3} (hf : ContMDiff (𝓡 2) (𝓡 3) ∞ f)
    (N : S2 -> S2)
    (hN : ∀ (p : S2) (w : E3),
      (∀ u, inner Real w (mfderiv (𝓡 2) (𝓡 3) f p u) = 0) ↔
        ∃ c : Real, w = c • (N p : E3))
    (v p : S2) :
    mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (v : E3) (f q)) p = 0 ↔
      N p = v ∨ N p = -v := by
  have hzero : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (v : E3) (f q)) p = 0 ↔
      ∀ u, inner Real (v : E3) (mfderiv (𝓡 2) (𝓡 3) f p u) = 0 := by
    constructor
    · intro h u
      rw [← mfderiv_height_apply hf, h]
      rfl
    · intro h
      ext u
      exact (mfderiv_height_apply hf v p u).trans (h u)
  rw [hzero, hN p v]
  constructor
  · rintro ⟨c, hc⟩
    rcases eq_or_eq_neg_of_smul v (N p) hc with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, neg_neg])
  · rintro (h | h)
    · exact ⟨1, by rw [h, one_smul]⟩
    · exact ⟨-1, by rw [h]; simp⟩



theorem exists_height_with_finite_critical_points
    (f : sphere (0 : EuclideanSpace Real (Fin 3)) 1 ->
      EuclideanSpace Real (Fin 3))
    (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f) :
    ∃ v : sphere (0 : EuclideanSpace Real (Fin 3)) 1,
      {p : sphere (0 : EuclideanSpace Real (Fin 3)) 1 |
        mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun q => inner Real (v : EuclideanSpace Real (Fin 3)) (f q)) p = 0}.Finite := by
  obtain ⟨N, hN, hnormal⟩ := exists_smooth_unit_normal f hf
  have hne : (univ : Set S2).Nonempty := by
    obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : E3))).mpr
      (by norm_num : (0 : Real) ≤ 1)
    exact ⟨⟨v, hv⟩, mem_univ _⟩
  obtain ⟨v, _, hv, hnv⟩ := exists_antipodal_regular_values_sphere hN isOpen_univ hne
  refine ⟨v, ((finite_fiber_of_regular_value_sphere hN hv).union
    (finite_fiber_of_regular_value_sphere hN hnv)).subset ?_⟩
  intro p hp
  exact (height_critical_iff_normal hf.contMDiff N hnormal v p).mp hp

end Poincare.Manifold.Schoenflies
