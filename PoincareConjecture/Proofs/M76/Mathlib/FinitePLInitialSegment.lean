import PoincareConjecture.Proofs.M76.Mathlib.CommonAffineSegmentPartition

set_option autoImplicit false

open Set

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem FinitePiecewiseAffineOn.exists_initial_affine_segment
    {f : E → F} {s : Set E} (hf : FinitePiecewiseAffineOn f s)
    (a : ℝ →ᴬ[ℝ] E) (ha : MapsTo a (Icc (0 : ℝ) 1) s) :
    ∃ δ ∈ Ioc (0 : ℝ) 1, ∃ A : ℝ →ᴬ[ℝ] F,
      EqOn (f ∘ a) A (Icc 0 δ) := by
  classical
  obtain ⟨n, t, ht, ht0, ht1, hformula⟩ :=
    hf.exists_common_affine_segment_partition (ι := Unit) (fun _ => a) (fun _ => ha)
  have hδpos : 0 < t (1 : Fin (n + 2)) := by
    rw [← ht0]
    exact ht (by simp)
  have hδle : t (1 : Fin (n + 2)) ≤ 1 := by
    rw [← ht1]
    exact ht.monotone (Fin.le_last _)
  refine ⟨t (1 : Fin (n + 2)), ⟨hδpos, hδle⟩, ?_⟩
  simpa [ht0] using hformula () (0 : Fin (n + 1))

theorem FinitePiecewiseAffineOn.exists_positive_initial_slope
    {f : E → ℝ} {s : Set E} (hf : FinitePiecewiseAffineOn f s)
    (a : ℝ →ᴬ[ℝ] E) (ha : MapsTo a (Icc (0 : ℝ) 1) s)
    (hzero : f (a 0) = 0) (hpos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < f (a t)) :
    ∃ δ ∈ Ioc (0 : ℝ) 1, ∃ m : ℝ, 0 < m ∧
      ∀ t ∈ Icc 0 δ, f (a t) = t * m := by
  obtain ⟨δ, hδ, A, hA⟩ := hf.exists_initial_affine_segment a ha
  have hA0 : A 0 = 0 := (hA ⟨le_rfl, hδ.1.le⟩).symm.trans hzero
  have hlin (t : ℝ) : A t = t * A 1 := by
    have h := A.toAffineMap.apply_lineMap (0 : ℝ) 1 t
    change A (AffineMap.lineMap 0 1 t) = AffineMap.lineMap (A 0) (A 1) t at h
    simpa [AffineMap.lineMap_apply_ring', hA0] using h
  have hδval : f (a δ) = δ * A 1 := (hA ⟨hδ.1.le, le_rfl⟩).trans (hlin δ)
  have hm : 0 < A 1 := by
    have hp := hpos δ hδ
    rw [hδval] at hp
    nlinarith [hδ.1]
  exact ⟨δ, hδ, A 1, hm, fun t ht => (hA ht).trans (hlin t)⟩

end Geometry
