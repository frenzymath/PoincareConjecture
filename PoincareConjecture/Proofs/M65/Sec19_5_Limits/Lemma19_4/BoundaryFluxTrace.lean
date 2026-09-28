import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FluxIntegral










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m65Metric_pairing_continuousOn (g : RiemannianMetric n M)
    (f : LoopPlane → M) (V W : (z : LoopPlane) → TangentSpace (𝓡 n) (f z))
    {S : Set LoopPlane}
    (hV : ContinuousOn (fun z => (⟨f z, V z⟩ : TangentBundle (𝓡 n) M)) S)
    (hW : ContinuousOn (fun z => (⟨f z, W z⟩ : TangentBundle (𝓡 n) M)) S) :
    ContinuousOn (fun z => g.inner (f z) (V z) (W z)) S := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  exact hV.inner_bundle hW



noncomputable def m65PlaneTraceFlux (g : RiemannianMetric n M)
    (f : LoopPlane → M) (V : (z : LoopPlane) → TangentSpace (𝓡 n) (f z))
    (E : (z : LoopPlane) → Fin 2 → TangentSpace (𝓡 n) (f z))
    (z : LoopPlane) : LoopPlane :=
  WithLp.toLp 2 (fun i => g.inner (f z) (V z) (E z i))



theorem m65PlaneTraceFlux_continuousOn (g : RiemannianMetric n M)
    (f : LoopPlane → M) (V : (z : LoopPlane) → TangentSpace (𝓡 n) (f z))
    (E : (z : LoopPlane) → Fin 2 → TangentSpace (𝓡 n) (f z))
    {S : Set LoopPlane}
    (hV : ContinuousOn (fun z => (⟨f z, V z⟩ : TangentBundle (𝓡 n) M)) S)
    (hE : ∀ i, ContinuousOn (fun z => (⟨f z, E z i⟩ : TangentBundle (𝓡 n) M)) S) :
    ContinuousOn (m65PlaneTraceFlux g f V E) S := by
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn
    (continuousOn_pi.mpr fun i => m65Metric_pairing_continuousOn g f V (fun z => E z i)
      hV (hE i))



theorem m65PlaneTraceFlux_inner (g : RiemannianMetric n M)
    (f : LoopPlane → M) (V : (z : LoopPlane) → TangentSpace (𝓡 n) (f z))
    (E : (z : LoopPlane) → Fin 2 → TangentSpace (𝓡 n) (f z))
    (z w : LoopPlane) :
    inner ℝ (m65PlaneTraceFlux g f V E z) w =
      g.inner (f z) (V z) (∑ i : Fin 2, w i • E z i) := by
  simp [PiLp.inner_apply, m65PlaneTraceFlux]

end PoincareConjecture
