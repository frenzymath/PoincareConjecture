import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusChartCollar
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Sweep.AnnulusJoin













set_option autoImplicit false

noncomputable section

open Set
open scoped Topology Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareConjecture.M64



theorem exists_disjoint_chart_boundary_annulus
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M}
    {cchart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hn : 3 ≤ n) {eps : ℝ} (heps : 0 < eps)
    {d c : ℝ → M}
    (hsourceD : ∀ x, d x ∈ cchart.source)
    (hsourceC : ∀ x, c x ∈ cchart.source)
    (hcoordD : ContDiff ℝ 1 (fun x => cchart (d x)))
    (hcoordC : ContDiff ℝ 1 (fun x => cchart (c x)))
    (hperiodD : Function.Periodic d curvePeriod)
    (hperiodC : Function.Periodic c curvePeriod)
    (hchartSymm : ContMDiffOn (𝓡 n) (𝓡 n) 1 cchart.symm cchart.target)
    (A0 : M64Annulus g d c) :
    ∃ v : EuclideanSpace ℝ (Fin n), ‖v‖ < eps ∧
      (∀ x, cchart (c x) + v ∈ cchart.target) ∧
      Function.Periodic (fun x => cchart.symm (cchart (c x) + v)) curvePeriod ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1
        (fun x => cchart.symm (cchart (c x) + v)) ∧
      Disjoint (range d)
        (range (fun x => cchart.symm (cchart (c x) + v))) ∧
      ∃ A : M64Annulus g d
          (fun x => cchart.symm (cchart (c x) + v)),
        A.map = m64AnnulusJoinMap A0.map
          (fun p : LoopPlane => cchart.symm
            (cchart (c (p 0)) + (p 1) • v)) := by
  obtain ⟨v, hv, hvtarget, hvperiod, hcprime, hvdisjoint, C, hCmap⟩ :=
    exists_chart_displaced_boundary_collar hn heps hsourceD hsourceC hcoordD
      hcoordC hperiodD hperiodC hchartSymm
  obtain ⟨A, hAmap⟩ := m64Annulus_join A0 C
  refine ⟨v, hv, hvtarget, hvperiod, hcprime, hvdisjoint, A, ?_⟩
  rw [hAmap, hCmap]

end PoincareConjecture.M64
