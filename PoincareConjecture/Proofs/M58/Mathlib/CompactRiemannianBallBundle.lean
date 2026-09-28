import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.ProperSpace











set_option autoImplicit false

open Bundle Set Filter
open scoped Topology

universe u v w

namespace PoincareConjecture.Proofs.M58

variable {B : Type u} [TopologicalSpace B]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]



theorem continuous_bundle_norm : Continuous (fun v : TotalSpace F E => ‖v.2‖) := by
  have h : Continuous (fun v : TotalSpace F E => inner ℝ v.2 v.2) :=
    continuous_id.inner_bundle continuous_id
  simpa only [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)] using h.sqrt



theorem isCompact_bundle_norm_le [T2Space B] [LocallyCompactSpace B] [ProperSpace F]
    {K : Set B} (hK : IsCompact K) (R : ℝ) :
    IsCompact {v : TotalSpace F E | v.proj ∈ K ∧ ‖v.2‖ ≤ R} := by
  classical
  have hlocal (x : B) : ∃ L : Set B, ∃ C : ℝ,
      L ∈ 𝓝 x ∧ IsCompact L ∧ 0 < C ∧
      ∀ y ∈ L, y ∈ (trivializationAt F E x).baseSet ∧
        ‖(trivializationAt F E x).continuousLinearMapAt ℝ y‖ < C := by
    obtain ⟨C, hC, hbound⟩ := eventually_norm_trivializationAt_lt F E x
    have hbase := (trivializationAt F E x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' x)
    obtain ⟨L, hLx, hLU, hL⟩ :=
      LocallyCompactSpace.local_compact_nhds x _ (inter_mem hbase hbound)
    exact ⟨L, C, hLx, hL, hC, hLU⟩
  choose L C hLx hL hC hbound using hlocal
  obtain ⟨s, -, hs⟩ := hK.elim_nhds_subcover L (fun x _ => hLx x)
  let Q (x : B) : Set (TotalSpace F E) :=
    (fun z : B × F => TotalSpace.mk' F z.1 ((trivializationAt F E x).symm z.1 z.2)) ''
      (L x ×ˢ Metric.closedBall (0 : F) (C x * R))
  have hQ (x : B) : IsCompact (Q x) :=
    ((hL x).prod (isCompact_closedBall _ _)).image_of_continuousOn
      ((trivializationAt F E x).continuousOn_symm.mono
        (prod_mono (fun y hy => (hbound x y hy).1) (subset_univ _)))
  have hclosed : IsClosed {v : TotalSpace F E | v.proj ∈ K ∧ ‖v.2‖ ≤ R} :=
    (hK.isClosed.preimage (FiberBundle.continuous_proj F E :
      Continuous (TotalSpace.proj : TotalSpace F E → B))).inter
      (isClosed_le continuous_bundle_norm continuous_const)
  apply (s.isCompact_biUnion (fun x _ => hQ x)).of_isClosed_subset hclosed
  intro v hv
  obtain ⟨x, hxs, hx⟩ := mem_iUnion₂.mp (hs hv.1)
  apply mem_iUnion₂.mpr
  refine ⟨x, hxs, ?_⟩
  let e := trivializationAt F E x
  have hvbase : v.proj ∈ e.baseSet := (hbound x v.proj hx).1
  refine ⟨(v.proj, e.continuousLinearMapAt ℝ v.proj v.2), ⟨hx, ?_⟩, ?_⟩
  · rw [mem_closedBall_zero_iff]
    exact ((e.continuousLinearMapAt ℝ v.proj).le_opNorm v.2).trans
      (mul_le_mul (hbound x v.proj hx).2.le hv.2 (norm_nonneg _) (hC x).le)
  · change TotalSpace.mk' F v.proj (e.symm v.proj
      (e.continuousLinearMapAt ℝ v.proj v.2)) = v
    rw [← e.symmL_apply (R := ℝ) hvbase, e.symmL_continuousLinearMapAt hvbase]

end PoincareConjecture.Proofs.M58
