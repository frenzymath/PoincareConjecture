import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.Pointed
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Bounds.Ricci
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Basic









noncomputable section
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open Poincare.GromovHausdorff
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture

private theorem exists_strictMono_tendsto_atTop_of_unbounded
    (a : ℕ → ℝ) (hlarge : ∀ C : ℝ, ∃ j : ℕ, C < a j) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto (a ∘ phi) atTop atTop := by
  classical
  have hnext (i k : ℕ) : ∃ j : ℕ, i < j ∧ (k : ℝ) < a j := by
    obtain ⟨C, hC⟩ := ((Set.finite_Iic i).image a).bddAbove
    obtain ⟨j, hj⟩ := hlarge (max C (k : ℝ))
    refine ⟨j, ?_, (le_max_right _ _).trans_lt hj⟩
    by_contra hji
    have := hC ⟨j, not_lt.mp hji, rfl⟩
    exact (not_le_of_gt ((le_max_left _ _).trans_lt hj)) this
  choose next hindex hvalue using hnext
  let phi : ℕ → ℕ := fun k => Nat.rec (next 0 0) (fun i j => next j (i + 1)) k
  have hphi : StrictMono phi := strictMono_nat_of_lt_succ fun k => hindex (phi k) (k + 1)
  have hbound (k : ℕ) : (k : ℝ) ≤ a (phi k) := by
    cases k with
    | zero => exact (hvalue 0 0).le
    | succ k => exact (hvalue (phi k) (k + 1)).le
  exact ⟨phi, hphi, tendsto_atTop_mono hbound tendsto_natCast_atTop_atTop⟩




theorem exists_subseq_proper_geodesic_pointed_limit_scalar_integral_tendsto_atTop
    {n : ℕ} {M : ℕ → Type}
    [∀ j, TopologicalSpace (M j)] [∀ j, T3Space (M j)]
    [∀ j, MeasurableSpace (M j)] [∀ j, BorelSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)] [∀ j, PreconnectedSpace (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j)) (p : ∀ j, M j)
    (hn : 1 ≤ n) (hcomplete : ∀ j, PoincareConjecture.MetricComplete (g j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (hlarge : ∀ C : ℝ, ∃ j : ℕ,
      C < ∫ x in (g j).ball (p j) 1, (D j).scalarCurvature x ∂(g j).volumeMeasure) :
    ∃ phi : ℕ → ℕ, ∃ S : CompatiblePointedCompactSystem.{0},
      StrictMono phi ∧ ProperSpace S.completedLimit.carrier ∧
      (∀ x y : S.completedLimit.carrier, ∃ γ : ℝ → S.completedLimit.carrier,
        γ 0 = x ∧ γ 1 = y ∧
        ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist x y) ∧
      PointedGHConvergesUnbounded
        (fun j => (g (phi j)).toBasedMetricSpace (p (phi j))) S.completedLimit ∧
      Tendsto
        (fun j => ∫ x in (g (phi j)).ball (p (phi j)) 1,
          (D (phi j)).scalarCurvature x ∂(g (phi j)).volumeMeasure)
        atTop atTop := by
  obtain ⟨psi, hpsi, hdiv⟩ := exists_strictMono_tendsto_atTop_of_unbounded
    (fun j => ∫ x in (g j).ball (p j) 1, (D j).scalarCurvature x ∂(g j).volumeMeasure)
    hlarge
  have hRic : ∀ j x v,
      -(((n : ℝ) - 1) * 1) * (g j).inner x v v ≤ (D j).ricci x v v := by
    intro j x v
    exact (D j).ricci_quadratic_lower_bound_of_sectionalCurvature_lower_bound
      x 1 (hsec j x) v
  obtain ⟨theta, S, htheta, hproper, hgeodesic, hconverges⟩ :=
    RiemannianMetric.exists_subseq_proper_geodesic_pointed_limit_of_ricci_lower_bound
      (fun j => g (psi j)) (fun j => p (psi j)) hn 1 (by norm_num)
      (fun j => hcomplete (psi j)) (fun j => D (psi j)) (fun j => hRic (psi j))
  exact ⟨psi ∘ theta, S, hpsi.comp htheta, hproper, hgeodesic, hconverges,
    hdiv.comp htheta.tendsto_atTop⟩

end PoincareConjecture
