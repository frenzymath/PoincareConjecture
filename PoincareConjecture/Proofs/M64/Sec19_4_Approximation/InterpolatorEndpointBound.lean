import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.TwoEndpointMinimizingInterpolator
import PoincareConjecture.Proofs.M58.Mathlib.LocalTangentMap
import PoincareConjecture.Proofs.M58.Mathlib.CompactRiemannianBallBundle

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem m64_continuous_endpoint_tangent_input :
    Continuous (fun v : ℝ × (TangentBundle (𝓡 n) M × TangentBundle (𝓡 n) M) =>
      (⟨(v.1, v.2.1.proj, v.2.2.proj), (0, v.2.1.2, v.2.2.2)⟩ :
        TangentBundle (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (ℝ × (M × M)))) := by
  have ht : Continuous
      (fun v : ℝ × (TangentBundle (𝓡 n) M × TangentBundle (𝓡 n) M) =>
        (⟨v.1, 0⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_fst.prodMk continuous_const)
  have hp : Continuous
      (fun v : ℝ × (TangentBundle (𝓡 n) M × TangentBundle (𝓡 n) M) =>
        (⟨(v.2.1.proj, v.2.2.proj), (v.2.1.2, v.2.2.2)⟩ :
          TangentBundle ((𝓡 n).prod (𝓡 n)) (M × M))) :=
    (contMDiff_equivTangentBundleProd_symm (I := 𝓡 n) (I' := 𝓡 n)
      (M := M) (M' := M) (n := 0)).continuous.comp continuous_snd
  exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ))
    (I' := (𝓡 n).prod (𝓡 n)) (M := ℝ) (M' := M × M) (n := 0)).continuous.comp
      (ht.prodMk hp)

theorem m64_exists_interpolator_endpoint_bound [T2Space M]
    (g : RiemannianMetric n M) (hcompact : IsCompact (univ : Set M))
    (H : ℝ × (M × M) → M) {L : Set (M × M)} (hL : IsCompact L)
    (hH : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ L,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) 1 H x)
    (S : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ L,
      ∀ v : TangentSpace (𝓡 n) x.2.1,
        g.tangentNorm x.2.1 v ≤ S →
      ∀ w : TangentSpace (𝓡 n) x.2.2,
        g.tangentNorm x.2.2 w ≤ S →
        g.tangentNorm (H x)
          (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) H x (0, v, w)) ≤
            B := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let D := mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) H
  let Q : Set (TangentBundle (𝓡 n) M) :=
    {v | v.proj ∈ (univ : Set M) ∧ ‖v.2‖ ≤ S}
  have hQ : IsCompact Q := Proofs.M58.isCompact_bundle_norm_le hcompact S
  let K : Set (ℝ × (TangentBundle (𝓡 n) M × TangentBundle (𝓡 n) M)) :=
    (Icc (0 : ℝ) 1 ×ˢ (Q ×ˢ Q)) ∩ {v | (v.2.1.proj, v.2.2.proj) ∈ L}
  have hproj : Continuous
      (fun v : ℝ × (TangentBundle (𝓡 n) M × TangentBundle (𝓡 n) M) =>
        (v.2.1.proj, v.2.2.proj)) :=
    ((FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))).comp
      continuous_snd.fst).prodMk
        ((FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n))).comp
          continuous_snd.snd)
  have hK : IsCompact K := (isCompact_Icc.prod (hQ.prod hQ)).inter_right
    (hL.isClosed.preimage hproj)
  have hc : ContinuousOn
      (fun v : ℝ × (TangentBundle (𝓡 n) M × TangentBundle (𝓡 n) M) =>
        ‖D (v.1, v.2.1.proj, v.2.2.proj) (0, v.2.1.2, v.2.2.2)‖) K := by
    intro v hv
    have hbase : (v.1, v.2.1.proj, v.2.2.proj) ∈ Icc (0 : ℝ) 1 ×ˢ L :=
      ⟨hv.1.1, hv.2⟩
    exact (Proofs.M58.continuous_bundle_norm.continuousAt.comp
      ((Proofs.M58.continuousAt_tangentMap_of_contMDiffAt
        (hH _ hbase)).comp
          m64_continuous_endpoint_tangent_input.continuousAt)).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x hx v hv w hw
  have hmem : (x.1, (⟨x.2.1, v⟩ : TangentBundle (𝓡 n) M),
      (⟨x.2.2, w⟩ : TangentBundle (𝓡 n) M)) ∈ K :=
    ⟨⟨hx.1, ⟨mem_univ _, hv⟩, ⟨mem_univ _, hw⟩⟩, hx.2⟩
  exact (le_abs_self _).trans ((hB _ hmem).trans (le_max_left _ _))

theorem m64_interpolator_endpoint_bound_on_short_tube [T2Space M]
    (g : RiemannianMetric n M) (hcompact : IsCompact (univ : Set M))
    {r : ℝ} (hr : 0 < r) (H : ℝ × (M × M) → M)
    (hH : ContMDiffOn
      (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) ∞ H
      (Ioo (-1 : ℝ) 2 ×ˢ
        {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r}))
    (S : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ p q : M,
      g.edist p q ≤ ENNReal.ofReal (r / 2) →
      ∀ v : TangentSpace (𝓡 n) p, g.tangentNorm p v ≤ S →
      ∀ w : TangentSpace (𝓡 n) q, g.tangentNorm q w ≤ S →
        g.tangentNorm (H (t, p, q))
          (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) H
            (t, p, q) (0, v, w)) ≤ B := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let L : Set (M × M) := {pq | g.edist pq.1 pq.2 ≤ ENNReal.ofReal (r / 2)}
  have hdist : Continuous (fun pq : M × M => g.edist pq.1 pq.2) :=
    continuous_edist
  have hL : IsCompact L := (isClosed_le hdist continuous_const).isCompact
  have hU : IsOpen {pq : M × M | g.edist pq.1 pq.2 < ENNReal.ofReal r} :=
    isOpen_lt hdist continuous_const
  have hHAt : ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ L,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 n).prod (𝓡 n))) (𝓡 n) 1 H x := by
    intro x hx
    have ht : x.1 ∈ Ioo (-1 : ℝ) 2 := by
      constructor <;> linarith [hx.1.1, hx.1.2]
    have hpq : g.edist x.2.1 x.2.2 < ENNReal.ofReal r :=
      hx.2.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr (by linarith))
    exact (hH.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds ⟨ht, hpq⟩)).of_le
      (m := 1) (by norm_num)
  obtain ⟨B, hB, hbound⟩ :=
    m64_exists_interpolator_endpoint_bound g hcompact H hL hHAt S
  refine ⟨B, hB, ?_⟩
  intro t ht p q hpq v hv w hw
  exact hbound (t, p, q) ⟨ht, hpq⟩ v hv w hw

end PoincareConjecture
