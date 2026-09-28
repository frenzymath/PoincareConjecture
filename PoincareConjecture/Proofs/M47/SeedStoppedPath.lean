import PoincareConjecture.Proofs.M47.SeedFirstCrossing










set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]




theorem exists_seed_path_from_crossing_or_end
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (gamma : ℝ → M) (hgamma : ContinuousOn gamma (Icc 0 1))
    {H L : ℝ} (hL : 0 ≤ L) (hlow : D.scalarCurvature (gamma 0) ≤ H)
    (hspeed : ∀ v ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (0 : ℝ) 1,
      g.edist (gamma v) (gamma w) ≤ ENNReal.ofReal (L * |v - w|)) :
    ∃ delta : ℝ → M, delta 1 = gamma 0 ∧
      delta 0 ∈ connectedComponent (gamma 0) ∧
      ContinuousOn delta (Icc 0 1) ∧
      (∀ v ∈ Icc (0 : ℝ) 1, D.scalarCurvature (delta v) ≤ H) ∧
      (∀ v ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (0 : ℝ) 1,
        g.edist (delta v) (delta w) ≤ ENNReal.ofReal (L * |v - w|)) ∧
      (D.scalarCurvature (delta 0) = H ∨ delta 0 = gamma 1) := by
  classical
  by_cases hcross : ∃ b ∈ Icc (0 : ℝ) 1, H ≤ D.scalarCurvature (gamma b)
  · obtain ⟨b, hb, hhigh⟩ := hcross
    let f : ℝ → ℝ := fun v => b * v
    let path := gamma ∘ f
    have hmaps : MapsTo f (Icc 0 1) (Icc 0 1) := by
      intro v hv
      exact ⟨mul_nonneg hb.1 hv.1,
        (mul_le_mul_of_nonneg_left hv.2 hb.1).trans (by simpa only [mul_one] using hb.2)⟩
    have hpath : ContinuousOn path (Icc 0 1) :=
      hgamma.comp (by fun_prop : ContinuousOn f (Icc 0 1)) hmaps
    have hzero : path 0 = gamma 0 := by simp only [path, Function.comp_apply, f, mul_zero]
    have hone : path 1 = gamma b := by simp only [path, Function.comp_apply, f, mul_one]
    have hpathSpeed : ∀ v ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (0 : ℝ) 1,
        g.edist (path v) (path w) ≤ ENNReal.ofReal (L * |v - w|) := by
      intro v hv w hw
      have h := hspeed _ (hmaps hv) _ (hmaps hw)
      have hdiff : |f v - f w| = b * |v - w| := by
        rw [show f v - f w = b * (v - w) by dsimp only [f]; ring,
          abs_mul, abs_of_nonneg hb.1]
      rw [hdiff] at h
      exact h.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (abs_nonneg _) hb.2) hL))
    obtain ⟨delta, hd1, hcomp, hvalue, hd, hbound, hdspeed⟩ :=
      exists_reversed_seed_crossing_path g D path hpath (H := H) (L := L) hL
        (by simpa only [hzero] using hlow) (by simpa only [hone] using hhigh) hpathSpeed
    refine ⟨delta, hd1.trans hzero, ?_, hd, hbound, hdspeed, Or.inl hvalue⟩
    simpa only [hzero] using hcomp
  · let f : ℝ → ℝ := fun v => 1 - v
    let delta := gamma ∘ f
    have hmaps : MapsTo f (Icc 0 1) (Icc 0 1) := by
      intro v hv
      dsimp only [f]
      constructor <;> linarith [hv.1, hv.2]
    have hzero : delta 0 = gamma 1 := by simp only [delta, Function.comp_apply, f, sub_zero]
    have hone : delta 1 = gamma 0 := by simp only [delta, Function.comp_apply, f, sub_self]
    have hcomp : gamma 1 ∈ connectedComponent (gamma 0) :=
      (isPreconnected_Icc.image gamma hgamma).subset_connectedComponent
        ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
    refine ⟨delta, hone, hzero ▸ hcomp,
      hgamma.comp (by fun_prop : ContinuousOn f (Icc 0 1)) hmaps, ?_, ?_, Or.inr hzero⟩
    · intro v hv
      exact (lt_of_not_ge (fun h => hcross ⟨f v, hmaps hv, h⟩)).le
    · intro v hv w hw
      have h := hspeed _ (hmaps hv) _ (hmaps hw)
      have hdiff : |f v - f w| = |v - w| := by
        rw [show f v - f w = w - v by dsimp only [f]; ring, abs_sub_comm]
      simpa only [delta, Function.comp_apply, hdiff] using h

end PoincareConjecture.Proofs.M47
