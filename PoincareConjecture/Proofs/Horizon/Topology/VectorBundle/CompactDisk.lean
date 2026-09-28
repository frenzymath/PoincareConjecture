import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Topology

namespace Poincare.VectorBundle

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]


lemma continuous_fiber_norm : Continuous (fun q : TotalSpace F E => ‖q.2‖) := by
  have h : Continuous (fun q : TotalSpace F E => inner ℝ q.2 q.2) :=
    Continuous.inner_bundle (F := F) continuous_id continuous_id
  simpa only [Function.comp_def, real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_norm] using
    Real.continuous_sqrt.comp h



theorem isCompact_disk_over [T2Space B] [LocallyCompactSpace B]
    [FiniteDimensional ℝ F] {K : Set B} (hK : IsCompact K) (R : ℝ) :
    IsCompact {q : TotalSpace F E | q.1 ∈ K ∧ ‖q.2‖ ≤ R} := by
  classical
  choose C hCpos hC using eventually_norm_trivializationAt_lt F E
  let e := fun x : B => trivializationAt F E x
  have hnb (x : B) : {y | y ∈ (e x).baseSet ∧
      ‖(e x).continuousLinearMapAt ℝ y‖ < C x} ∈ 𝓝 x :=
    inter_mem ((e x).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)) (hC x)
  choose L hLmem hLsub hLcompact using fun x => local_compact_nhds (hnb x)
  obtain ⟨s, -, hs⟩ := hK.elim_nhds_subcover L (fun x _ => hLmem x)
  let A := fun x => (e x).toOpenPartialHomeomorph.symm ''
    (L x ×ˢ Metric.closedBall (0 : F) (C x * max R 0))
  have hA (x : B) : IsCompact (A x) := by
    apply ((hLcompact x).prod (isCompact_closedBall _ _)).image_of_continuousOn
    apply (e x).toOpenPartialHomeomorph.continuousOn_symm.mono
    intro z hz
    exact (e x).mem_target.mpr (hLsub x hz.1).1
  have hclosed : IsClosed {q : TotalSpace F E | q.1 ∈ K ∧ ‖q.2‖ ≤ R} :=
    (hK.isClosed.preimage (FiberBundle.continuous_proj F E)).inter
      (isClosed_le continuous_fiber_norm continuous_const)
  apply (s.isCompact_biUnion fun x _ => hA x).of_isClosed_subset hclosed
  intro q hq
  obtain ⟨x, hx, hqx⟩ := mem_iUnion₂.mp (hs hq.1)
  apply mem_iUnion₂.mpr
  refine ⟨x, hx, e x q, ?_, (e x).symm_apply_apply ((e x).mem_source.mpr (hLsub x hqx).1)⟩
  have hbase : q.1 ∈ (e x).baseSet := (hLsub x hqx).1
  refine ⟨?_, ?_⟩
  · simpa only [(e x).coe_fst ((e x).mem_source.mpr hbase)] using hqx
  · rw [Metric.mem_closedBall, dist_zero_right]
    have heval : (e x q).2 = (e x).continuousLinearMapAt ℝ q.1 q.2 := by
      simp only [Trivialization.continuousLinearMapAt_apply,
        Trivialization.linearMapAt_apply, hbase, if_true]
    rw [heval]
    calc
      _ ≤ ‖(e x).continuousLinearMapAt ℝ q.1‖ * ‖q.2‖ :=
        (e x).continuousLinearMapAt ℝ q.1 |>.le_opNorm q.2
      _ ≤ C x * max R 0 :=
        mul_le_mul (hLsub x hqx).2.le (hq.2.trans (le_max_left _ _))
          (norm_nonneg _) (hCpos x).le


theorem isCompact_sphere_over [T2Space B] [LocallyCompactSpace B]
    [FiniteDimensional ℝ F] {K : Set B} (hK : IsCompact K) (R : ℝ) :
    IsCompact {q : TotalSpace F E | q.1 ∈ K ∧ ‖q.2‖ = R} := by
  apply (isCompact_disk_over hK R).of_isClosed_subset
    ((hK.isClosed.preimage (FiberBundle.continuous_proj F E)).inter
      (isClosed_eq continuous_fiber_norm continuous_const))
  exact fun _ h => ⟨h.1, h.2.le⟩

end Poincare.VectorBundle
