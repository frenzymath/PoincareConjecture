import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.CoordinateRicci
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.TimeDerivative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.ChangeMetric

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {J : Set ℝ} (Fseq : ℕ → RicciFlow 3 M J)
  (g : ℝ → RiemannianMetric 3 M) (hg : RiemannianMetric.IsSmoothFamilyOn g J)
  (hspace : ∀ t ∈ J, ∀ x : M, ∀ r : ℕ, r ≤ 2 → ∀ a b : Fin 3,
    Tendsto (fun k => iteratedFDeriv ℝ r
      (fun y => ((Fseq k).metric t).pullbackCoefficients (extChartAt (𝓡 3) x).symm y
        (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) (extChartAt (𝓡 3) x x)) atTop
      (𝓝 (iteratedFDeriv ℝ r
        (fun y => (g t).pullbackCoefficients (extChartAt (𝓡 3) x).symm y
          (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) (extChartAt (𝓡 3) x x))))
  (htime : ∀ t ∈ J, ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
    Tendsto (fun k => derivWithin (fun s => ((Fseq k).metric s).inner x v w) J t)
      atTop (𝓝 (derivWithin (fun s => (g s).inner x v w) J t)))

include Fseq hg hspace htime

theorem terminalGerms_equation_of_included_jets
    (D : ∀ t, LeviCivitaData (g t)) :
    ∀ t ∈ J, ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s => (g s).inner x v w) (-2 * (D t).ricci x v w) J t := by
  have hJ : UniqueDiffOn ℝ J := uniqueDiffOn_convex (Fseq 0).interval.convex
    ((Fseq 0).interval.convex.nontrivial_iff_nonempty_interior.mp (Fseq 0).nontrivial)
  intro t ht x v w
  have hRic := LeviCivitaData.tendsto_ricci_of_coordinate_jets
    (fun k => (Fseq k).connection t) (D t) x v w (hspace t ht x)
  have heq (k : ℕ) : derivWithin (fun s => ((Fseq k).metric s).inner x v w) J t =
      -2 * ((Fseq k).connection t).ricci x v w :=
    ((Fseq k).equation t ht x v w).derivWithin (hJ t ht)
  have hlimit : derivWithin (fun s => (g s).inner x v w) J t =
      -2 * (D t).ricci x v w := by
    apply tendsto_nhds_unique (htime t ht x v w)
    simpa only [heq] using hRic.const_mul (-2)
  rw [← hlimit]
  exact ((hg.contDiffWithinAt_inner_time ht x v w).differentiableWithinAt
    (by simp)).hasDerivWithinAt

theorem terminalGerms_exists_closed_ricciFlow :
    ∃ F : RicciFlow 3 M J, F.metric = g := by
  let D : ∀ t, LeviCivitaData (g t) :=
    fun t => ((Fseq 0).connection 0).withMetric (g t)
  exact ⟨{
    metric := g
    connection := D
    interval := (Fseq 0).interval
    nontrivial := (Fseq 0).nontrivial
    smooth := hg
    equation := terminalGerms_equation_of_included_jets Fseq g hg hspace htime D }, rfl⟩

end PoincareConjecture.M47
