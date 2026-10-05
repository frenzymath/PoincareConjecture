import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Scalar.Ratio

/-!
# Scalar-supremum stability on a cap

Uniform scalar convergence on the cap controls the curvature supremum and
its inverse curvature scales. These are the scales in the diameter and
volume inequalities in Morgan--Tian, Proposition 9.79, used in Claim 9.90,
p. 241.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}

/-- Uniform convergence on a cap implies convergence of the scalar suprema. -/
theorem scalar_sup_tendsto (A : CapCertificate g) {f : ℕ → M → ℝ}
    (hconv : TendstoUniformlyOn f A.connection.scalarCurvature atTop A.carrier) :
    Tendsto (fun k => sSup (range (fun x : A.carrier => f k x))) atTop
      (𝓝 (scalarCurvatureSupOn g A.connection A.carrier)) := by
  obtain ⟨p, hp⟩ := A.core_nonempty
  have hp' := A.core_subset_carrier hp
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv (ε / 2) (by positivity)] with k hk
  have hclose (x : M) (hx : x ∈ A.carrier) :
      |f k x - A.connection.scalarCurvature x| < ε / 2 := by
    simpa only [Real.dist_eq, abs_sub_comm] using hk x hx
  have hbounded : BddAbove (range (fun x : A.carrier => f k x)) := by
    refine ⟨scalarCurvatureSupOn g A.connection A.carrier + ε / 2, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hx := (abs_lt.mp (hclose x x.property)).2
    have hs := A.scalar_le_sup x.property
    linarith
  have hupper : sSup (range (fun x : A.carrier => f k x)) ≤
      scalarCurvatureSupOn g A.connection A.carrier + ε / 2 := by
    let S : Set ℝ := range (fun x : A.carrier => f k x)
    have hS : S.Nonempty := ⟨f k p, ⟨⟨p, hp'⟩, rfl⟩⟩
    change sSup S ≤ _
    refine csSup_le hS ?_
    rintro _ ⟨x, rfl⟩
    have hx := (abs_lt.mp (hclose x x.property)).2
    have hs := A.scalar_le_sup x.property
    linarith
  have hlower : scalarCurvatureSupOn g A.connection A.carrier ≤
      sSup (range (fun x : A.carrier => f k x)) + ε / 2 := by
    unfold scalarCurvatureSupOn
    refine csSup_le ⟨A.connection.scalarCurvature p, ⟨⟨p, hp'⟩, rfl⟩⟩ ?_
    rintro _ ⟨x, rfl⟩
    have hx := (abs_lt.mp (hclose x x.property)).1
    have hs := le_csSup hbounded (mem_range_self x)
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Every real power of the positive curvature supremum varies continuously. -/
theorem scalar_sup_rpow_tendsto (A : CapCertificate g) {f : ℕ → M → ℝ}
    (hconv : TendstoUniformlyOn f A.connection.scalarCurvature atTop A.carrier)
    (q : ℝ) :
    Tendsto (fun k => (sSup (range (fun x : A.carrier => f k x))) ^ q) atTop
      (𝓝 ((scalarCurvatureSupOn g A.connection A.carrier) ^ q)) := by
  exact (A.scalar_sup_tendsto hconv).rpow_const (Or.inl A.scalar_sup_pos.ne')

end PoincareMT.CapCertificate
