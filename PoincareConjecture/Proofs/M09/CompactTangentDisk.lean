import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]

theorem isCompact_tangentDisk (g : RiemannianMetric n M) (K : Set M)
    (hK : IsCompact K) (R : ℝ) (hR : 0 ≤ R) :
    IsCompact {z : TangentBundle (𝓡 n) M |
      z.proj ∈ K ∧ g.inner z.proj z.2 z.2 ≤ R} := by
  classical
  letI : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let e := fun x : M ↦ trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  have hlocal (x : M) : ∃ B : ℝ, 0 < B ∧ ∃ L : Set M,
      IsCompact L ∧ x ∈ interior L ∧
      ∀ y ∈ L, y ∈ (e x).baseSet ∧ ‖(e x).continuousLinearMapAt ℝ y‖ < B := by
    obtain ⟨B, hB, hnorm⟩ := eventually_norm_trivializationAt_lt
      (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : M → Type _) x
    have hb : (e x).baseSet ∈ 𝓝 x :=
      (e x).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)
    obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp (Filter.inter_mem hb hnorm)
    obtain ⟨L, hLc, hxL, hLU⟩ := exists_compact_subset hUopen hxU
    exact ⟨B, hB, L, hLc, hxL, fun y hy ↦ hUsub (hLU hy)⟩
  choose B hB L hLc hxL hL using hlocal
  obtain ⟨S, _, hcover⟩ := hK.elim_nhds_subcover (fun x ↦ interior (L x))
    (fun x _ ↦ isOpen_interior.mem_nhds (hxL x))
  let C := fun x : M ↦ (e x).toOpenPartialHomeomorph.symm ''
    (L x ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (B x * Real.sqrt R))
  have hCc (x : M) : IsCompact (C x) := by
    apply ((hLc x).prod (isCompact_closedBall _ _)).image_of_continuousOn
    apply (e x).toOpenPartialHomeomorph.continuousOn_symm.mono
    intro z hz
    exact (e x).mem_target.mpr (hL x z.1 hz.1).1
  have hclosed : IsClosed {z : TangentBundle (𝓡 n) M |
      z.proj ∈ K ∧ g.inner z.proj z.2 z.2 ≤ R} := by
    have hi : Continuous (fun z : TangentBundle (𝓡 n) M ↦ g.inner z.proj z.2 z.2) :=
      Continuous.inner_bundle (b := fun z : TangentBundle (𝓡 n) M ↦ z.proj)
        (v := fun z ↦ z.2) (w := fun z ↦ z.2) continuous_id continuous_id
    exact (hK.isClosed.preimage (FiberBundle.continuous_proj _ _)).inter
      (isClosed_le hi continuous_const)
  apply (S.isCompact_biUnion (fun x _ ↦ hCc x)).of_isClosed_subset hclosed
  intro z hz
  obtain ⟨x, hxS, hx⟩ := Set.mem_iUnion₂.mp (hcover hz.1)
  have hzL : z.proj ∈ L x := interior_subset hx
  have hzb : z.proj ∈ (e x).baseSet := (hL x z.proj hzL).1
  have hzs : z ∈ (e x).source := (e x).mem_source.mpr hzb
  have hnorm : ‖z.2‖ ≤ Real.sqrt R := by
    rw [norm_eq_sqrt_real_inner]
    exact Real.sqrt_le_sqrt hz.2
  have hcoord : ‖((e x) z).2‖ ≤ B x * Real.sqrt R := by
    rw [← (e x).continuousLinearMapAt_apply_of_mem ℝ hzb z.2]
    calc
      _ ≤ ‖(e x).continuousLinearMapAt ℝ z.proj‖ * ‖z.2‖ :=
        ((e x).continuousLinearMapAt ℝ z.proj).le_opNorm z.2
      _ ≤ B x * ‖z.2‖ :=
        mul_le_mul_of_nonneg_right (hL x z.proj hzL).2.le (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (hB x).le
  apply Set.mem_iUnion₂.mpr
  refine ⟨x, hxS, (e x) z, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa only [(e x).coe_fst hzs] using hzL
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hcoord
  · exact (e x).toOpenPartialHomeomorph.left_inv hzs

end PoincareConjecture.Proofs.M09
