import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Curvature.MovingJets

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem exists_shifted_scalar_metric_germ
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (φ : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n))
    (hφ : ∀ᶠ y in 𝓝 x, ContMDiffAt (𝓡 n) (𝓡 n) ∞ φ y ∧
      Function.Injective (mfderiv (𝓡 n) (𝓡 n) φ y)) :
    ∃ gd : Σ h : RiemannianMetric n (EuclideanSpace ℝ (Fin n)), LeviCivitaData h,
      (gd.1.euclideanCoefficients =ᶠ[𝓝 0]
        fun y ↦ g.pullbackCoefficients φ (y + x)) ∧
      gd.2.scalarCurvature 0 = D.scalarCurvature (φ x) := by
  obtain ⟨V, hVφ, hVo, hxV⟩ := mem_nhds_iff.mp hφ
  let U := (fun y ↦ y + x) ⁻¹' V
  have hU : IsOpen U := hVo.preimage (continuous_id.add continuous_const)
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ U := by simpa only [U, mem_preimage, zero_add] using hxV
  have hshift : ContMDiff (𝓡 n) (𝓡 n) ∞ (fun y : EuclideanSpace ℝ (Fin n) ↦ y + x) :=
    (contDiff_id.add contDiff_const).contMDiff
  have hd (y) (hy : y ∈ U) :
      mfderiv (𝓡 n) (𝓡 n) (fun z ↦ φ (z + x)) y = mfderiv (𝓡 n) (𝓡 n) φ (y + x) := by
    have hh := mfderiv_comp y ((hVφ hy).1.mdifferentiableAt (by simp))
      (hshift.mdifferentiable (by simp) y)
    change mfderiv (𝓡 n) (𝓡 n) (φ ∘ (fun z ↦ z + x)) y = _
    rw [hh]
    ext v
    simp +instances [mfderiv_eq_fderiv, fderiv_add_const]
    rfl
  have hpos : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g.pullbackCoefficients φ (y + x) v v := by
    intro y hy v hv
    apply g.pos (φ (y + x))
    intro hz
    apply hv
    apply (hVφ hy).2
    rw [map_zero]
    convert! hz using 1
  obtain ⟨h, Dh, W, hWo, h0W, hWU, heq⟩ := RiemannianMetric.exists_local_realization hU h0
    (fun y ↦ g.pullbackCoefficients φ (y + x))
    (fun y hy ↦ ((g.contDiffAt_pullbackCoefficients (hVφ hy).1).comp y
      (contDiff_id.add contDiff_const).contDiffAt).contDiffWithinAt)
    (fun y _ v w ↦ g.symm _ _ _) hpos
  refine ⟨⟨h, Dh⟩, Filter.Eventually.mono (hWo.mem_nhds h0W) heq, ?_⟩
  have hh := Dh.scalarCurvature_eq_of_local_isometry D (f := fun y ↦ φ (y + x)) hWo
    (fun y hy ↦ ((hVφ (hWU hy)).1.comp y hshift.contMDiffAt).contMDiffWithinAt)
    (fun y hy v w ↦ by
      change h.euclideanCoefficients y v w = _
      rw [heq y hy]
      simp +instances only [hd y (hWU hy)]
      rfl) h0W
  simpa only [zero_add] using hh

theorem tendsto_scalarCurvature_of_moving_scalar_pullback_jets
    {α : Type*} {l : Filter α} [l.NeBot] {n : ℕ}
    {M : α → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} (D : ∀ k, LeviCivitaData (g k))
    (φ : ∀ k, EuclideanSpace ℝ (Fin n) → M k)
    {h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (Dh : LeviCivitaData h)
    (x : α → EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin n))
    (hφ : ∀ᶠ k in l, ∀ᶠ z in 𝓝 (x k), ContMDiffAt (𝓡 n) (𝓡 n) ∞ (φ k) z ∧
      Function.Injective (mfderiv (𝓡 n) (𝓡 n) (φ k) z))
    (hjets : ∀ r : ℕ, r ≤ 2 → ∀ a b : Fin n,
      Tendsto (fun k ↦ iteratedFDeriv ℝ r (fun z ↦
        (g k).pullbackCoefficients (φ k) z (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b)) (x k)) l
        (𝓝 (iteratedFDeriv ℝ r (fun z ↦ h.inner z (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b)) y))) :
    Tendsto (fun k ↦ (D k).scalarCurvature (φ k (x k))) l
      (𝓝 (Dh.scalarCurvature y)) := by
  have hreal := hφ.mono fun k hk ↦ exists_shifted_scalar_metric_germ (D k) (φ k) (x k) hk
  obtain ⟨gd, hgd⟩ := hreal.choice
  obtain ⟨hd, hhd, hnorm⟩ := exists_shifted_scalar_metric_germ Dh id y (Eventually.of_forall (fun z ↦ by
    refine ⟨contMDiffAt_id, ?_⟩
    rw [mfderiv_id]
    exact Function.injective_id))
  have hid : h.pullbackCoefficients id = h.euclideanCoefficients := by
    ext z v w
    simp +instances [RiemannianMetric.pullbackCoefficients, mfderiv_id,
      RiemannianMetric.euclideanCoefficients]
    rfl
  rw [hid] at hhd
  have hj (r : ℕ) (hr : r ≤ 2) (a b : Fin n) :
      Tendsto (fun k ↦ iteratedFDeriv ℝ r (fun z ↦ (gd k).1.euclideanCoefficients z
        (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) 0) l
        (𝓝 (iteratedFDeriv ℝ r (fun z ↦ hd.1.euclideanCoefficients z
          (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) 0)) := by
    have heq : (fun z ↦ hd.1.inner z (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b)) =ᶠ[𝓝 0]
        (fun z ↦ h.inner (z + y) (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b)) := hhd.mono (fun z hz ↦ congrArg
            (fun B ↦ B (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) hz)
    have heq' := (heq.iteratedFDeriv ℝ r).self_of_nhds
    change iteratedFDeriv ℝ r (fun z ↦ hd.1.euclideanCoefficients z
        (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) 0 =
      iteratedFDeriv ℝ r ((fun z ↦ h.euclideanCoefficients z
        (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) ∘
          (fun z ↦ z + y)) 0 at heq'
    have hs := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun z ↦ h.euclideanCoefficients z
      (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) r y 0
    have heq'' := heq'.trans hs
    simp only [zero_add] at heq''
    rw [heq'']
    apply (hjets r hr a b).congr'
    filter_upwards [hgd] with k hk
    have hk' : (fun z ↦ (gd k).1.inner z (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b)) =ᶠ[𝓝 0]
        (fun z ↦ (g k).pullbackCoefficients (φ k) (z + x k)
          (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) :=
      hk.1.mono (fun z hz ↦ congrArg
        (fun B ↦ B (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) hz)
    have hkj := (hk'.iteratedFDeriv ℝ r).self_of_nhds
    change iteratedFDeriv ℝ r (fun z ↦ (gd k).1.euclideanCoefficients z
        (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) 0 =
      iteratedFDeriv ℝ r ((fun z ↦ (g k).pullbackCoefficients (φ k) z
        (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) ∘
          (fun z ↦ z + x k)) 0 at hkj
    have hks := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun z ↦ (g k).pullbackCoefficients (φ k) z
      (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)) r (x k) 0
    simpa only [zero_add] using (hkj.trans hks).symm
  have ht := tendsto_scalarCurvature_of_scalar_metric_jets (fun k ↦ (gd k).2) hd.2 0
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis hj
  rw [hnorm] at ht
  exact ht.congr' (hgd.mono fun _ hk ↦ hk.2)

end PoincareConjecture.LeviCivitaData
