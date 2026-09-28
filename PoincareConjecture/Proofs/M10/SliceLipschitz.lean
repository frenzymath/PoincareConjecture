import PoincareConjecture.Proofs.M10.SpacetimeLipschitz

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}

set_option backward.isDefEq.respectTransparency false in

theorem reducedLength_slice_locallyLipschitz
    (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hwindow : Icc (T - τmax) T ⊆ J) (p : M)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric T).toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨(F.metric T).inner, (F.metric T).toContinuousRiemannianMetric.continuous,
        fun _ _ _ ↦ rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
    LocallyLipschitz (fun q ↦ reducedLength F T p q τ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨(F.metric T).inner, (F.metric T).toContinuousRiemannianMetric.continuous,
      fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hfull := reducedLength_locallyLipschitz hL hDifferential hwindow p
  change LocallyLipschitzOn (univ ×ˢ Ioo 0 τmax)
    (fun z : M × ℝ ↦ reducedLength F T p z.1 z.2) at hfull
  intro q
  obtain ⟨K, U, hU, hLip⟩ := hfull (x := (q, τ)) ⟨mem_univ _, hτ, hmax⟩
  rw [nhdsWithin_eq_nhds.mpr ((isOpen_univ.prod isOpen_Ioo).mem_nhds
    (show (q, τ) ∈ (univ : Set M) ×ˢ Ioo 0 τmax from ⟨mem_univ _, hτ, hmax⟩))] at hU
  refine ⟨K, (fun x : M ↦ (x, τ)) ⁻¹' U,
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds hU, ?_⟩
  simpa only [mul_one, Function.comp_def] using
    hLip.comp (LipschitzWith.prodMk_right τ).lipschitzOnWith (mapsTo_preimage _ _)

end PoincareConjecture.M10
