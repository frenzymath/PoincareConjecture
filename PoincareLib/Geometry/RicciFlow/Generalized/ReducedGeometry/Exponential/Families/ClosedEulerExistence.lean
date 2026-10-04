import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.ODE.Local.ClosedODELocalExistence
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Families.ClosedEulerODE

/-!
# Local families for the actual closed Euler phase

Morgan-Tian Lemma 6.18, pp. 113-114. M08's actual phase is smooth
on the closed time slab and open phase domain. Restricting the slab
preserves its genuine spatial derivatives. The closed Picard family
thus solves the actual phase equation on its own clipped interval.
-/

set_option autoImplicit false
-- The retained chart coefficient operators use the standard tangent models.
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The actual closed Euler phase is unchanged when its time set
is restricted at a retained point. The spatial derivatives are
genuine derivatives on the open chart target, as required by
equation (6.5) and Lemma 6.18, pp. 108-109, 113-114. -/
theorem closedChartEulerPhase_restrict {J C D : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x₀ : M)
    (htime : ∀ s ∈ C, T - s ^ 2 ∈ J) (hDC : D ⊆ C) {s : ℝ} (hs : s ∈ D)
    {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hz : z.1 ∈ (extChartAt (𝓡 n) x₀).target) :
    M08.closedChartEulerPhase F T x₀ D s z = M08.closedChartEulerPhase F T x₀ C s z := by
  have hU := isOpen_extChartAt_target (I := 𝓡 n) x₀
  have hB := (M08.hasFDerivAt_spatialWithin hU _
    (M08.chartActionMetric_closed_contDiffOn F T x₀ (fun t ht => htime t (hDC ht))) hs hz).unique
    (M08.hasFDerivAt_spatialWithin hU _
      (M08.chartActionMetric_closed_contDiffOn F T x₀ htime) (hDC hs) hz)
  have hP := (M08.hasFDerivAt_spatialWithin hU _
    (M08.chartActionPotential_closed_contDiffOn F hM04 T x₀
      (fun t ht => htime t (hDC ht))) hs hz).unique
    (M08.hasFDerivAt_spatialWithin hU _
      (M08.chartActionPotential_closed_contDiffOn F hM04 T x₀ htime) (hDC hs) hz)
  simp only [M08.closedChartEulerPhase, hB, hP]

/-- A local jointly continuous family of actual closed Euler phases
exists through all sufficiently nearby initial phases and remains
inside the chart. Each time curve is smooth, including its closed
endpoints. This is the local existence part of Lemma 6.18, pp. 113-114. -/
theorem exists_closedChartEulerPhase_family {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x₀ : M)
    {a b s₀ : ℝ} (hab : a < b) (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    (hs₀ : s₀ ∈ Icc a b)
    {z₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hz₀ : z₀.1 ∈ (extChartAt (𝓡 n) x₀).target) :
    ∃ δ > (0 : ℝ), ∃ r > (0 : ℝ),
      let C := Icc (max a (s₀ - δ)) (min b (s₀ + δ))
      max a (s₀ - δ) < min b (s₀ + δ) ∧
      ∃ α : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ →
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ContinuousOn α (closedBall z₀ r ×ˢ C) ∧
        ∀ z ∈ closedBall z₀ r, α (z, s₀) = z ∧
          (∀ s ∈ C, (α (z, s)).1 ∈ (extChartAt (𝓡 n) x₀).target) ∧
          ContDiffOn ℝ ∞ (fun s => α (z, s)) C ∧
          ∀ s ∈ C, HasDerivWithinAt (fun t => α (z, t))
            (M08.closedChartEulerPhase F T x₀ C s (α (z, s))) C s := by
  obtain ⟨δ, hδ, r, hr, hcd, α, hc, hα⟩ := closedODE_exists_local_family hab
    ((isOpen_extChartAt_target (I := 𝓡 n) x₀).prod isOpen_univ)
    (Function.uncurry (M08.closedChartEulerPhase F T x₀ (Icc a b)))
    (M08.closedChartEulerPhase_contDiffOn F hM04 T x₀ (uniqueDiffOn_Icc hab) htime)
    hs₀ ⟨hz₀, mem_univ _⟩
  refine ⟨δ, hδ, r, hr, hcd, α, hc, ?_⟩
  intro z hz
  obtain ⟨hi, hmap, hsm, hd⟩ := hα z hz
  refine ⟨hi, fun s hs => (hmap hs).1, hsm, ?_⟩
  intro s hs
  have hsub : Icc (max a (s₀ - δ)) (min b (s₀ + δ)) ⊆ Icc a b :=
    fun t ht => ⟨(le_max_left _ _).trans ht.1, ht.2.trans (min_le_left _ _)⟩
  rw [closedChartEulerPhase_restrict F hM04 T x₀ htime hsub hs (hmap hs).1]
  exact hd s hs

end PoincareMT.M14
