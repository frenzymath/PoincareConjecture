import PoincareLib.Geometry.RicciFlow.Curvature.Calculus
import PoincareLib.Geometry.RicciFlow.Splitting.NullEvolution
import PoincareLib.Geometry.RicciFlow.Splitting.KernelTransport.Ricci
import PoincareLib.Geometry.RicciFlow.Splitting.MaximumPrinciple.RicciPropagation
import PoincareLib.Geometry.RicciFlow.Splitting.ParallelField
import PoincareLib.Geometry.Curvature.Operator.SectionalBounds

/-!
# Backward persistence of parallel gradients

All Ricci partial-trace thresholds propagate by the scalar strong maximum
principle. The resulting spatial nullity and null-section energy identity
give backward inclusion of the actual Ricci kernels across every rank.
Connection variation then preserves the fixed terminal parallel field,
including both endpoints. Metric duality identifies the same gradient.

This supplies the global fixed-field conclusion needed in Kleiner--Lott,
Proposition 41.13, p. 2678, by the tensor maximum-principle route of
Appendix A, Theorem A.7, p. 2841. The alternative holonomy route is
Cook--Kotschwar, Corollary 4.1 and Section 4.0.1, p. 7.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.RicciFlow.Splitting

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

/-- Nonnegative sectional curvature forces backward inclusion of the
actual Ricci kernels on the whole closed slab, in every corank. -/
theorem ricciKernel_antitoneOn
    (hC : RicciFlowCurvatureCalculus.{u}) (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (x : M) : AntitoneOn (fun t => ricciKernel (F.connection t) x) (Icc a b) := by
  apply ricciKernel_antitone_of_derivative_annihilates hC F x
    (ricciNullity_antitoneOn hC hab F hsec x)
  intro t ht v hv w
  exact ricci_hasDerivWithinAt_zero_of_null_vector hC F hsec
    (fun s hs => ricciNullity_eq_on_positive_slice hC hab F hsec hs) ht x v (hv v) w

/-- A smooth terminal parallel field stays parallel as the same global
field on the original manifold at every earlier time. -/
theorem terminal_parallel_field_persists
    (hC : RicciFlowCurvatureCalculus.{u}) (hab : a < b)
    (F : RicciFlow n M (Icc a b))
    (hsec : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V))
    (hterminal : ∀ x, (F.connection b).connection V x = 0) :
    ∀ t ∈ Icc a b, ∀ x, (F.connection t).connection V x = 0 := by
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hn (x : M) : V x ∈ ricciKernel (F.connection b) x := by
    rw [mem_ricciKernel]
    exact ricci_eq_zero_of_parallel_field (F.connection b)
      (hC.tensor_calculus n M (F.metric b) (F.connection b)) V hV hterminal x
  have hnull (t : ℝ) (ht : t ∈ Ioc a b) (x : M) :
      (F.connection t).ricci x (V x) (V x) = 0 := by
    have hv := ricciKernel_antitoneOn hC hab F hsec x ⟨ht.1.le, ht.2⟩ hb ht.2 (hn x)
    exact (mem_ricciKernel _ x (V x)).mp hv (V x)
  intro t ht x
  rw [connection_eq_terminal_of_ricci_null hC hab F hsec V hV hnull t ht x]
  exact hterminal x

omit [T2Space M] in
/-- A unit parallel terminal gradient persists on the full closed slab,
with the same function and global vector field in every dimension. -/
theorem backward_persistence_of_parallel_gradient
    [T3Space M]
    (hC : RicciFlowCurvatureCalculus.{u}) (_hn : 1 ≤ n)
    (hab : a < b) (F : RicciFlow n M (Icc a b))
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hcurv : ∀ t ∈ Icc a b, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ x : M,
      (F.connection t).curvatureTensorNorm x ≤ K)
    (f : M → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : RiemannianMetric.HasUnitGradient (F.connection b) f)
    (hzero : RiemannianMetric.HasZeroHessian (F.connection b) f) :
    ∀ t ∈ Icc a b,
      (F.connection t).gradient f = (F.connection b).gradient f ∧
        RiemannianMetric.HasUnitGradient (F.connection t) f ∧
          RiemannianMetric.HasZeroHessian (F.connection t) f := by
  have hsec (t : ℝ) (ht : t ∈ Icc a b) :
      (F.connection t).NonnegativeSectionalCurvature :=
    fun x u v => (F.connection t).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hcurv t ht x) u v
  have hX := (F.connection b).contMDiff_gradient hf
  have hterminal (x : M) :
      (F.connection b).connection ((F.connection b).gradient f) x = 0 := by
    ext u
    exact RiemannianMetric.connection_gradient_eq_zero_of_hasZeroHessian hf hzero x u
  have hpar := terminal_parallel_field_persists hC hab F hsec
    ((F.connection b).gradient f) hX hterminal
  let hfield := ParallelFieldData.of_parallel_field hC F f
    ((F.connection b).gradient f) (fun _ => rfl) hf hzero hX
    (fun t ht x u => by rw [hpar t ⟨ht.1, ht.2.le⟩ x]; rfl)
  exact backward_persistence_of_parallel_field_data hab F hcomplete hcurv hbound
    f hf hunit hzero hfield

end PoincareMT.RicciFlow.Splitting
