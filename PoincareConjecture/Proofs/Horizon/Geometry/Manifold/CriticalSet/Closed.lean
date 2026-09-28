import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle ChartedSpace IsManifold
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem isClosed_setOf_mfderiv_eq_zero {h : M → Real}
    (hh : ContMDiff I 𝓘(Real, Real) 1 h) :
    IsClosed {p : M | mfderiv I 𝓘(Real, Real) h p = 0} := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  let A := inTangentCoordinates I 𝓘(Real, Real) id h
    (mfderiv I 𝓘(Real, Real) h) p
  have hA : ContinuousAt A p :=
    ((hh p).mfderiv_const (m := 0) (by simp)).continuousAt
  have hself : A p = mfderiv I 𝓘(Real, Real) h p := by
    dsimp [A]
    rw [inTangentCoordinates_eq id h _ (mem_chart_source _ p) (mem_chart_source _ (h p))]
    ext u
    change tangentCoordChange 𝓘(Real, Real) (h p) (h p) (h p)
      (mfderiv I 𝓘(Real, Real) h p (tangentCoordChange I p p p u)) = _
    rw [tangentCoordChange_self (mem_extChartAt_source p),
      tangentCoordChange_self (mem_extChartAt_source (h p))]
    rfl
  have ha : A p ≠ 0 := by rwa [hself]
  filter_upwards [hA.eventually_ne ha] with q hq
  intro hzero
  change mfderiv I 𝓘(Real, Real) h q = 0 at hzero
  apply hq
  simp [A, inTangentCoordinates, ContinuousLinearMap.inCoordinates, hzero]

theorem isCompact_critical_values [CompactSpace M] {h : M → Real}
    (hh : ContMDiff I 𝓘(Real, Real) 1 h) :
    IsCompact (h '' {p : M | mfderiv I 𝓘(Real, Real) h p = 0}) :=
  (isClosed_setOf_mfderiv_eq_zero hh).isCompact.image hh.continuous

theorem isClosed_critical_values [CompactSpace M] {h : M → Real}
    (hh : ContMDiff I 𝓘(Real, Real) 1 h) :
    IsClosed (h '' {p : M | mfderiv I 𝓘(Real, Real) h p = 0}) :=
  (isCompact_critical_values hh).isClosed

end Poincare.Geometry.Manifold
