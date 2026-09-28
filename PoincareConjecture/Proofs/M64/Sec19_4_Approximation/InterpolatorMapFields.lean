import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.InterpolatorWitness













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

omit [T2Space M] in




theorem m64_interpolator_map_continuous
    {g : RiemannianMetric n M} {D : LeviCivitaData g}
    {N : ℕ} (polygon : M63GeodesicPolygon g D N)
    {gamma : ℝ → M} {U : Set (M × M)} {H : ℝ × (M × M) → M}
    (hH : ContMDiffOn
      ((𝓘(ℝ, ℝ)).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ U))
    (hgamma : Continuous gamma)
    (hpair_global : ∀ x : ℝ, (gamma x, polygon.map x) ∈ U)
    (f : LoopPlane → M)
    (hf : f = (fun p : LoopPlane =>
      H (p 1, gamma (p 0), polygon.map (p 0)))) :
    ContinuousOn f m64AnnulusDomain := by
  have hp0 : Continuous (fun p : LoopPlane => p 0) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  have hp1 : Continuous (fun p : LoopPlane => p 1) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1
  let input : LoopPlane → ℝ × (M × M) := fun p =>
    (p 1, (gamma (p 0), polygon.map (p 0)))
  have hinput : Continuous input := by
    exact hp1.prodMk ((hgamma.comp hp0).prodMk (polygon.continuous.comp hp0))
  have hmem : ∀ p ∈ m64AnnulusDomain,
      input p ∈ Ioo (-1 : ℝ) 2 ×ˢ U := by
    intro p hp
    change p 1 ∈ Ioo (-1 : ℝ) 2 ∧ (gamma (p 0), polygon.map (p 0)) ∈ U
    exact ⟨by
      constructor <;> linarith [hp.2.2.1, hp.2.2.2], hpair_global (p 0)⟩
  have hc := hH.continuousOn.comp hinput.continuousOn hmem
  simpa only [hf, input, Function.comp_def] using hc

omit [T2Space M] in



theorem m64_interpolator_map_periodic
    {g : RiemannianMetric n M} {D : LeviCivitaData g}
    {N : ℕ} (polygon : M63GeodesicPolygon g D N)
    {gamma : ℝ → M} {H : ℝ × (M × M) → M}
    (hgamma_periodic : Function.Periodic gamma curvePeriod)
    (f : LoopPlane → M)
    (hf : f = (fun p : LoopPlane =>
      H (p 1, gamma (p 0), polygon.map (p 0)))) :
    ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) =
        f (annulusPoint x s) := by
  intro x s
  rw [hf]
  change H (s, gamma (x + curvePeriod), polygon.map (x + curvePeriod)) =
    H (s, gamma x, polygon.map x)
  rw [hgamma_periodic x, polygon.periodic x]

end PoincareConjecture
