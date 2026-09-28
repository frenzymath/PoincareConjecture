import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.MetricConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Curvature
import Mathlib.Topology.UniformSpace.UniformApproximation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 8

open Set Filter Manifold Poincare.Gluing
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

private theorem exists_shifted_pullback_realization
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (φ : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n))
    (hφ : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ φ x) :
    ∃ gd : Σ h : RiemannianMetric n (EuclideanSpace ℝ (Fin n)), LeviCivitaData h,
      (gd.1.euclideanCoefficients =ᶠ[𝓝 0]
        fun y => g.pullbackCoefficients φ (y + x)) ∧
      gd.2.curvatureTensorNorm 0 = D.curvatureTensorNorm (φ x) := by
  obtain ⟨Φ, hx, hEq⟩ := hφ
  have hd (y) (hy : y ∈ Φ.source) :
      IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ φ y := ⟨Φ, hy, hEq⟩
  let U := (fun y => y + x) ⁻¹' Φ.source
  have hU : IsOpen U := Φ.open_source.preimage (continuous_id.add continuous_const)
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ U := by simpa [U] using hx
  have hshift : ContMDiff (𝓡 n) (𝓡 n) ∞ (fun y : EuclideanSpace ℝ (Fin n) => y + x) :=
    (contDiff_id.add contDiff_const).contMDiff
  have hderiv (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ U) :
      mfderiv (𝓡 n) (𝓡 n) (fun z => φ (z + x)) y =
        mfderiv (𝓡 n) (𝓡 n) φ (y + x) := by
    have hh := mfderiv_comp y ((hd (y + x) hy).mdifferentiableAt (by simp))
      (hshift.mdifferentiable (by simp) y)
    change mfderiv (𝓡 n) (𝓡 n) (φ ∘ (fun z => z + x)) y = _
    rw [hh]
    ext v
    simp +instances [mfderiv_eq_fderiv, fderiv_add_const]
    rfl
  obtain ⟨h, Dh, V, hV, h0V, hVU, heq⟩ :=
    RiemannianMetric.exists_local_realization hU h0
      (fun y => g.pullbackCoefficients φ (y + x))
      (fun y hy => ((g.contDiffAt_pullbackCoefficients (hd _ hy).contMDiffAt).comp y
        (contDiff_id.add contDiff_const).contDiffAt).contDiffWithinAt)
      (fun y _ v w => g.symm _ _ _)
      (by
        intro y hy v hv
        apply g.pos (φ (y + x))
        intro hz
        apply hv
        apply ((hd _ hy).mfderivToContinuousLinearEquiv (by simp)).injective
        change mfderiv (𝓡 n) (𝓡 n) φ (y + x) v =
          mfderiv (𝓡 n) (𝓡 n) φ (y + x) 0
        rw [map_zero]
        convert! hz using 1)
  refine ⟨⟨h, Dh⟩, Filter.Eventually.mono (hV.mem_nhds h0V) heq, ?_⟩
  have hh := Dh.curvatureTensorNorm_eq_of_local_isometry D
    (f := fun y => φ (y + x)) hV
    (fun y hy => (((hd _ (hVU hy)).contMDiffAt).comp y hshift.contMDiffAt).contMDiffWithinAt)
    (fun y hy v w => by
      change h.euclideanCoefficients y v w = _
      rw [heq y hy]
      simp +instances only [hderiv y (hVU hy)]
      rfl) h0V
  simpa only [zero_add] using hh

theorem tendsto_curvatureTensorNorm_of_moving_pullback_jets
    {α : Type*} {l : Filter α} [l.NeBot] {n : ℕ}
    {M : α → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} (D : ∀ k, LeviCivitaData (g k))
    (φ : ∀ k, EuclideanSpace ℝ (Fin n) → M k)
    {h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (Dh : LeviCivitaData h)
    (x : α → EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin n))
    (hφ : ∀ᶠ k in l, IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ (φ k) (x k))
    (hjets : ∀ r : ℕ, r ≤ 2 →
      Tendsto (fun k => iteratedFDeriv ℝ r ((g k).pullbackCoefficients (φ k)) (x k))
        l (𝓝 (iteratedFDeriv ℝ r h.euclideanCoefficients y))) :
    Tendsto (fun k => (D k).curvatureTensorNorm (φ k (x k))) l
      (𝓝 (Dh.curvatureTensorNorm y)) := by
  have hreal := hφ.mono fun k hk => exists_shifted_pullback_realization (D k) (φ k) (x k) hk
  obtain ⟨gd, hgd⟩ := hreal.choice
  obtain ⟨hd, hhd, hnorm⟩ := exists_shifted_pullback_realization Dh id y
    ((Diffeomorph.refl (𝓡 n) (EuclideanSpace ℝ (Fin n)) ∞).isLocalDiffeomorph y)
  have hid : h.pullbackCoefficients id = h.euclideanCoefficients := by
    ext z v w
    simp +instances [RiemannianMetric.pullbackCoefficients, mfderiv_id,
      RiemannianMetric.euclideanCoefficients]
    rfl
  rw [hid] at hhd
  have hj (r : ℕ) (hr : r ≤ 2) :
      Tendsto (fun k => iteratedFDeriv ℝ r (gd k).1.euclideanCoefficients 0) l
        (𝓝 (iteratedFDeriv ℝ r hd.1.euclideanCoefficients 0)) := by
    have heq := (hhd.iteratedFDeriv ℝ r).self_of_nhds
    simp only [iteratedFDeriv_comp_add_right, zero_add] at heq
    rw [heq]
    apply (hjets r hr).congr'
    filter_upwards [hgd] with k hk
    simpa only [iteratedFDeriv_comp_add_right, zero_add] using
      (hk.1.iteratedFDeriv ℝ r).self_of_nhds.symm
  let E := EuclideanSpace ℝ (Fin n)
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hs (r : ℕ) (hr : r ≤ 2) (a c : Fin n) :
      Tendsto (fun k => iteratedFDeriv ℝ r (fun z => (gd k).1.inner z (b a) (b c)) 0)
        l (𝓝 (iteratedFDeriv ℝ r (fun z => hd.1.inner z (b a) (b c)) 0)) := by
    let L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.apply ℝ ℝ (b c)).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (b a))
    have heval (g' : RiemannianMetric n E) :
        iteratedFDeriv ℝ r (fun z => g'.inner z (b a) (b c)) 0 =
          L.compContinuousMultilinearMap (iteratedFDeriv ℝ r g'.euclideanCoefficients 0) := by
      ext v
      exact g'.iteratedFDeriv_inner_eq 0 (b a) (b c) r v
    have ht := ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ
      (fun _ : Fin r => E) (E →L[ℝ] E →L[ℝ] ℝ) ℝ L).continuous.tendsto _).comp (hj r hr)
    change Tendsto (fun k => L.compContinuousMultilinearMap
      (iteratedFDeriv ℝ r (gd k).1.euclideanCoefficients 0)) l
      (𝓝 (L.compContinuousMultilinearMap (iteratedFDeriv ℝ r hd.1.euclideanCoefficients 0))) at ht
    rw [← heval hd.1] at ht
    exact ht.congr (fun k => (heval (gd k).1).symm)
  have ht := tendsto_curvatureTensorNorm_of_scalar_metric_jets (fun k => (gd k).2) hd.2 0 b hs
  rw [hnorm] at ht
  exact ht.congr' (hgd.mono fun _ hk => hk.2)

theorem exists_local_curvatureTensorNorm_lt_of_flat_pullback_jets
    {n : ℕ} {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} (D : ∀ k, LeviCivitaData (g k))
    (φ : ∀ k, EuclideanSpace ℝ (Fin n) → M k)
    {h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (Dh : LeviCivitaData h)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hφ : ∀ᶠ k in atTop, IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (φ k) Ω)
    (hjets : ∀ r : ℕ, r ≤ 2 → ∀ C, IsCompact C → C ⊆ Ω → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ r ((g k).pullbackCoefficients (φ k)))
      (iteratedFDeriv ℝ r h.euclideanCoefficients) atTop C)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Ω)
    (hflat : Dh.curvatureTensorNorm x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ Ω ∧
      ∀ᶠ k in atTop, ∀ y ∈ W, (D k).curvatureTensorNorm (φ k y) < ε := by
  obtain ⟨C, hC, hxC, hCΩ⟩ := exists_compact_between isCompact_singleton hΩ
    (singleton_subset_iff.mpr hx)
  have hCn : C ∈ 𝓝 x := mem_of_superset
    (isOpen_interior.mem_nhds (hxC (mem_singleton x))) interior_subset
  have hj (r : ℕ) (hr : r ≤ 2) :
      Tendsto (fun z : ℕ × EuclideanSpace ℝ (Fin n) =>
        iteratedFDeriv ℝ r ((g z.1).pullbackCoefficients (φ z.1)) z.2)
        (atTop ×ˢ 𝓝 x) (𝓝 (iteratedFDeriv ℝ r h.euclideanCoefficients x)) := by
    have hunif : TendstoUniformlyOn
        (fun z : ℕ × EuclideanSpace ℝ (Fin n) =>
          iteratedFDeriv ℝ r ((g z.1).pullbackCoefficients (φ z.1)))
        (iteratedFDeriv ℝ r h.euclideanCoefficients) (atTop ×ˢ 𝓝 x) C :=
      fun u hu => tendsto_fst.eventually (hjets r hr C hC hCΩ u hu)
    apply hunif.tendsto_comp
      ((ContDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top : (r : WithTop ℕ∞) ≤ ∞)
        (contDiff_iff_contDiffAt.mpr h.contDiffAt_euclideanCoefficients)).continuousWithinAt)
    rw [nhdsWithin_eq_nhds.mpr hCn]
    exact tendsto_snd
  have hd : ∀ᶠ z : ℕ × EuclideanSpace ℝ (Fin n) in atTop ×ˢ 𝓝 x,
      IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ (φ z.1) z.2 := by
    filter_upwards [hφ.prod_mk (hΩ.mem_nhds hx)] with z hz
    exact hz.1 ⟨z.2, hz.2⟩
  have ht := tendsto_curvatureTensorNorm_of_moving_pullback_jets
    (fun z : ℕ × EuclideanSpace ℝ (Fin n) => D z.1)
    (fun z => φ z.1) Dh Prod.snd x hd hj
  rw [hflat] at ht
  obtain ⟨P, hP, W, hW, hbound⟩ := eventually_prod_iff.mp (ht.eventually (gt_mem_nhds hε))
  obtain ⟨W', hW'W, hW'o, hxW'⟩ := mem_nhds_iff.mp (inter_mem hW (hΩ.mem_nhds hx))
  refine ⟨W', hW'o, hxW', fun y hy => (hW'W hy).2, ?_⟩
  exact hP.mono fun k hk y hy => hbound hk (hW'W hy).1

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.ChartDistance

private theorem isLocalDiffeomorphAt_source_parametrization
    {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)] (O : OverlapSystem (fun i => Piece U i))
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (A : Quotient O.setoid → M) (i : ι) (x : Piece U i) :
    letI := quotientChartedSpace U hU O
    IsManifold (𝓡 n) ∞ (Quotient O.setoid) →
    IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ A (O.include i x) →
    IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞
      (chartParametrization U hU (A ∘ O.include i)) (x : EuclideanSpace ℝ (Fin n)) := by
  let := quotientChartedSpace U hU O
  intro hQ hA
  let := hQ
  let c := quotientChart U hU O i
  have hc : c ∈ IsManifold.maximalAtlas (𝓡 n) ∞ (Quotient O.setoid) :=
    IsManifold.subset_maximalAtlas ⟨i, rfl⟩
  let d : PartialDiffeomorph (𝓡 n) (𝓡 n) (Quotient O.setoid)
      (EuclideanSpace ℝ (Fin n)) ∞ :=
    { toPartialEquiv := c.toPartialEquiv
      open_source := c.open_source
      open_target := c.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hc
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hc }
  have hx : (x : EuclideanSpace ℝ (Fin n)) ∈ d.symm.source := by
    simp [d, c, quotientChart_target]
  have hdA : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ A (d.symm x) := by
    simpa [d, c, quotientChart_symm_apply U hU O i x.property] using hA
  have hds : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ d.symm
      (x : EuclideanSpace ℝ (Fin n)) := ⟨d.symm, hx, Set.eqOn_refl _ _⟩
  apply (hds.comp (𝓡 n) M hdA).congr_of_eventuallyEq
  filter_upwards [(hU i).mem_nhds x.property] with y hy
  change chartParametrization U hU (A ∘ O.include i) y = A (c.symm y)
  rw [show y = (⟨y, hy⟩ : Piece U i).val from rfl,
    chartParametrization_apply, quotientChart_symm_apply U hU O i hy]
  rfl

theorem eventually_curvatureTensorNorm_lt_on_compact_of_local_metric_jets
    {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)] (O : OverlapSystem (fun i => Piece U i))
    {M : ℕ → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} (D : ∀ k, LeviCivitaData (g k))
    (h : ι → RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (Dh : ∀ i, LeviCivitaData (h i))
    (hflat : ∀ i x, x ∈ U i → (Dh i).curvatureTensorNorm x = 0)
    (A : ∀ k, Quotient O.setoid → M k) {V : Set (Quotient O.setoid)}
    (hjets : ∀ q ∈ V, ∃ i, ∃ W : Set (Piece U i), IsOpen W ∧
      q ∈ O.include i '' W ∧ O.include i '' W ⊆ V ∧
      ∀ m C, IsCompact C → C ⊆ Subtype.val '' W → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m ((g k).pullbackCoefficients
          (chartParametrization U hU (A k ∘ O.include i))))
        (iteratedFDeriv ℝ m (h i).euclideanCoefficients) atTop C)
    {K : Set (Quotient O.setoid)} (hK : IsCompact K) (hKV : K ⊆ V) :
    letI := quotientChartedSpace U hU O
    IsManifold (𝓡 n) ∞ (Quotient O.setoid) →
    (∀ᶠ k in atTop, IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ (A k) V) →
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ q ∈ K, (D k).curvatureTensorNorm (A k q) < ε := by
  let := quotientChartedSpace U hU O
  intro hQ hA ε hε
  let := hQ
  refine hK.induction_on (p := fun S => ∀ᶠ k in atTop,
    ∀ q ∈ S, (D k).curvatureTensorNorm (A k q) < ε) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall (by simp)
  · intro S T hST hT
    exact hT.mono fun _ hk q hq => hk q (hST hq)
  · intro S T hS hT
    filter_upwards [hS, hT] with k hkS hkT q hq
    exact hq.elim (hkS q) (hkT q)
  · intro q hqK
    obtain ⟨i, W, hW, ⟨x, hxW, rfl⟩, hWV, hj⟩ := hjets q (hKV hqK)
    have hΩ : IsOpen (Subtype.val '' W) :=
      (hU i).isOpenEmbedding_subtypeVal.isOpenMap _ hW
    have hlocal : ∀ᶠ k in atTop, IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞
        (chartParametrization U hU (A k ∘ O.include i)) (Subtype.val '' W) := by
      filter_upwards [hA] with k hk z
      obtain ⟨y, hyW, hyz⟩ := z.property
      rw [← hyz]
      exact isLocalDiffeomorphAt_source_parametrization U hU O (A k) i y hQ
        (hk ⟨O.include i y, hWV ⟨y, hyW, rfl⟩⟩)
    obtain ⟨B, hB, hxB, hBΩ, hb⟩ :=
      LeviCivitaData.exists_local_curvatureTensorNorm_lt_of_flat_pullback_jets D
        (fun k => chartParametrization U hU (A k ∘ O.include i)) (Dh i) hΩ
        hlocal (fun m _ C hC hCΩ => hj m C hC hCΩ) ⟨x, hxW, rfl⟩
        (hflat i x x.property) hε
    let W' : Set (Piece U i) := Subtype.val ⁻¹' B
    have hW' : IsOpen W' := hB.preimage continuous_subtype_val
    refine ⟨O.include i '' W', mem_nhdsWithin_of_mem_nhds
      (((O.include_isOpenEmbedding i).isOpenMap _ hW').mem_nhds ⟨x, hxB, rfl⟩), ?_⟩
    filter_upwards [hb] with k hk z hz
    obtain ⟨y, hy, rfl⟩ := hz
    simpa only [chartParametrization_apply, Function.comp_apply] using hk y hy

end PoincareConjecture.ChartDistance
