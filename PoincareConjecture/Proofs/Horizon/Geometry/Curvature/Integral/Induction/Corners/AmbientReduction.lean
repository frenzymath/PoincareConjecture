import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Normalized
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.Connected
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Isometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Similarity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.UniversalProperty

open Set Function Filter TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle Topology
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem PoincareConjecture.normalizedCornerScalarBound_of_connected_ambient
    (n m k : ℕ) (hdim : n = m+k) (δ H η C : ℝ)
    (hbound : ∀ (N : Type u) [TopologicalSpace N] [T3Space N]
      [MeasurableSpace N] [BorelSpace N]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
      [ConnectedSpace N],
      PoincareConjecture.NormalizedCornerScalarBound n m k hdim N δ H η C)
    (M : Type u) [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] :
    PoincareConjecture.NormalizedCornerScalarBound n m k hdim M δ H η C := by
  classical
  subst n
  intro g D hc hsec f h hf hh U hunit hpair hcross htight hhess F hF hreg c
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hF U hreg c
  let := isManifold_openFiber (m := m) hF U hreg c
  let L := openFiber F U c
  let incl := openFiberIncl F U c
  let gL : PoincareConjecture.RiemannianMetric m L :=
    PoincareConjecture.RiemannianMetric.Induced.pullbackMetric g incl
      (contMDiff_openFiberIncl (m := m) hF U hreg c)
      (injective_mfderiv_openFiberIncl (m := m) hF U hreg c)
  dsimp only
  intro hcompact hconnected hcomplete hdiam hbuffer K hK hKnonneg hKsec
  let : CompactSpace L := hcompact
  let : ConnectedSpace L := hconnected
  let z₀ : L := Classical.choice (inferInstance : Nonempty L)

  let W := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin (m+k))) (incl z₀)
  let gW := g.connectedComponentMetric (incl z₀)
  let DW := gW.leviCivitaData
  have hval : ContMDiff (𝓡 (m+k)) (𝓡 (m+k)) ∞ (Subtype.val : W → M) :=
    contMDiff_subtype_val
  let V : Opens W := ⟨Subtype.val ⁻¹' (U : Set M), U.isOpen.preimage continuous_subtype_val⟩
  let fw := fun i => f i ∘ (Subtype.val : W → M)
  let hw := fun i => h i ∘ (Subtype.val : W → M)
  let FW := F ∘ (Subtype.val : W → M)
  have hfw : ∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ (fw i) :=
    fun i => (hf i).comp contMDiff_subtype_val
  have hhw : ∀ i, ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ (hw i) :=
    fun i => (hh i).comp contMDiff_subtype_val
  have hFW : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ FW :=
    hF.comp contMDiff_subtype_val
  have hregW : ∀ x ∈ V, Surjective
      (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) FW x) := by
    intro x hx
    change Surjective (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) (fun y : W => F y) x)
    rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_restrict W F
      ((hF (x : M)).mdifferentiableAt (by simp))]
    exact hreg x hx
  have hcontained (x : L) : incl x ∈ W := by
    exact (contMDiff_openFiberIncl (m := m) hF U hreg c).continuous.mapsTo_connectedComponent
      z₀ (by simp)
  have hinv (x : W) : (mfderiv (𝓡 (m+k)) (𝓡 (m+k)) (Subtype.val : W → M) x).IsInvertible := by
    rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
    exact ⟨ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin (m+k))), rfl⟩
  have hinnerW (x : W) (v w : TangentSpace (𝓡 (m+k)) x) :
      gW.inner x v w = g.inner (x : M) v w := by
    change g.inner (x : M)
      (mfderiv (𝓡 (m+k)) (𝓡 (m+k)) (Subtype.val : W → M) x v)
      (mfderiv (𝓡 (m+k)) (𝓡 (m+k)) (Subtype.val : W → M) x w) = _
    rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
    rfl
  have hgrad (u : M → ℝ) (hu : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ u) (x : W) :
      DW.gradient (u ∘ Subtype.val) x = D.gradient u (x : M) := by
    have hp : mfderiv (𝓡 (m+k)) (𝓡 (m+k)) (Subtype.val : W → M) x
        (DW.gradient (u ∘ Subtype.val) x) = D.gradient u (x : M) := by
      rw [DW.gradient_comp_eq_mpullback D
        (hval.mdifferentiable (by simp) x)
        (hu.mdifferentiable (by simp) x) (hinv x) (fun _ _ => rfl)]
      exact (hinv x).self_apply_inverse _
    rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal] at hp
    exact hp
  have hhessW (u : M → ℝ) (hu : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ u)
      (x : W) (v w : TangentSpace (𝓡 (m+k)) x) :
      DW.hessian (u ∘ Subtype.val) x v w = D.hessian u (x : M) v w := by
    have ht := DW.hessian_comp_of_metric_pullback D (hval x)
      (Eventually.of_forall hinv) (Eventually.of_forall (fun _ _ _ => rfl))
      (hu (x : M)) v w
    rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal] at ht
    exact ht
  let := openFiberChartedSpace (m := m) hFW V hregW c
  let := isManifold_openFiber (m := m) hFW V hregW c
  let LW := openFiber FW V c
  let inclW := openFiberIncl FW V c
  let gLW := gW.openRegularFiberMetric hFW V hregW c

  let e₀ : L ≃ LW :=
    { toFun := fun x => ⟨⟨⟨x.1.1, hcontained x⟩, x.1.2⟩, x.2⟩
      invFun := fun x => ⟨⟨x.1.1.1, x.1.2⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e : L ≃ₘ⟮𝓡 m,𝓡 m⟯ LW :=
    { e₀ with
      contMDiff_toFun := by
        intro x
        apply (contMDiffAt_into_openFiber_iff (m := m) hFW c V hregW e₀ x).mpr
        apply (ContMDiffAt.subtypeVal_comp_iff W (inclW ∘ e₀) x).mp
        exact contMDiff_openFiberIncl (m := m) hF U hreg c x
      contMDiff_invFun := by
        intro x
        apply (contMDiffAt_into_openFiber_iff (m := m) hF c U hreg e₀.symm x).mpr
        exact (contMDiff_subtype_val.comp
          (contMDiff_openFiberIncl (m := m) hFW V hregW c)) x }
  have hmetric (x : L) (v w : TangentSpace (𝓡 m) x) :
      gL.inner x v w = gLW.inner (e x)
        (mfderiv (𝓡 m) (𝓡 m) e x v) (mfderiv (𝓡 m) (𝓡 m) e x w) := by
    have hcomp := mfderiv_comp x
      ((contMDiff_subtype_val.comp (contMDiff_openFiberIncl (m := m) hFW V hregW c)).mdifferentiable
        (by simp) (e x))
      (e.contMDiff.mdifferentiable (by simp) x)
    have hcomp' := mfderiv_comp (e x)
      (hval.mdifferentiable (by simp) (inclW (e x)))
      ((contMDiff_openFiberIncl (m := m) hFW V hregW c).mdifferentiable (by simp) (e x))
    rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal] at hcomp'
    change mfderiv (𝓡 m) (𝓡 (m+k)) (Subtype.val ∘ inclW) (e x) =
      mfderiv (𝓡 m) (𝓡 (m+k)) inclW (e x) at hcomp'
    rw [hcomp'] at hcomp
    change mfderiv (𝓡 m) (𝓡 (m+k)) incl x =
      (mfderiv (𝓡 m) (𝓡 (m+k)) inclW (e x)).comp
        (mfderiv (𝓡 m) (𝓡 m) e x) at hcomp
    change g.inner (incl x)
      (mfderiv (𝓡 m) (𝓡 (m+k)) incl x v)
      (mfderiv (𝓡 m) (𝓡 (m+k)) incl x w) = _
    change _ = gW.inner (inclW (e x))
      (mfderiv (𝓡 m) (𝓡 (m+k)) inclW (e x)
        (mfderiv (𝓡 m) (𝓡 m) e x v))
      (mfderiv (𝓡 m) (𝓡 (m+k)) inclW (e x)
        (mfderiv (𝓡 m) (𝓡 m) e x w))
    rw [hinnerW, hcomp]
    rfl

  have hnorm (u : M → ℝ) (hu : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,ℝ) ∞ u) (x : W) :
      gW.tangentNorm x (DW.gradient (u ∘ Subtype.val) x) =
        g.tangentNorm (x : M) (D.gradient u (x : M)) := by
    unfold PoincareConjecture.RiemannianMetric.tangentNorm
    rw [hinnerW, hgrad u hu]
  have hunitW : ∀ x ∈ V, ∀ i,
      gW.tangentNorm x (DW.gradient (fw i) x) ≤ 1 ∧
      gW.tangentNorm x (DW.gradient (hw i) x) ≤ 1 := by
    intro x hx i
    dsimp only [fw, hw]
    rw [hnorm (f i) (hf i) x, hnorm (h i) (hh i) x]
    exact hunit x hx i
  have hpairW : ∀ x ∈ V, ∀ i,
      gW.inner x (DW.gradient (fw i) x) (DW.gradient (hw i) x) ≤ -1+2*δ := by
    intro x hx i
    dsimp only [fw, hw]
    rw [hinnerW, hgrad (f i) (hf i) x, hgrad (h i) (hh i) x]
    exact hpair x hx i
  have hcrossW : ∀ x ∈ V, ∀ i j, i ≠ j →
      |gW.inner x (DW.gradient (fw i) x) (DW.gradient (fw j) x)| ≤ δ ∧
      |gW.inner x (DW.gradient (fw i) x) (DW.gradient (hw j) x)| ≤ δ ∧
      |gW.inner x (DW.gradient (hw i) x) (DW.gradient (fw j) x)| ≤ δ ∧
      |gW.inner x (DW.gradient (hw i) x) (DW.gradient (hw j) x)| ≤ δ := by
    intro x hx i j hij
    dsimp only [fw, hw]
    simp only [hinnerW]
    rw [hgrad (f i) (hf i) x, hgrad (h i) (hh i) x,
      hgrad (f j) (hf j) x, hgrad (h j) (hh j) x]
    exact hcross x hx i j hij
  have htightW : ∀ x ∈ V, ∀ i j, i ≠ j →
      gW.inner x (DW.gradient (fw i) x) (DW.gradient (fw j) x) ≤ 0 := by
    intro x hx i j hij
    dsimp only [fw]
    rw [hinnerW, hgrad (f i) (hf i) x, hgrad (f j) (hf j) x]
    exact htight x hx i j hij
  have hhessW' : ∀ x ∈ V, ∀ i v,
      DW.hessian (fw i) x v v ≤ H * gW.inner x v v ∧
      DW.hessian (hw i) x v v ≤ H * gW.inner x v v := by
    intro x hx i v
    dsimp only [fw, hw]
    rw [hhessW (f i) (hf i) x, hhessW (h i) (hh i) x, hinnerW]
    exact hhess x hx i v
  have hcW : PoincareConjecture.MetricComplete gW :=
    g.metricComplete_connectedComponentMetric hc (incl z₀)
  have hsecW : ∀ x (v w : TangentSpace (𝓡 (m+k)) x),
      -1 ≤ DW.sectionalCurvature x v w := by
    intro x v w
    rw [g.sectionalCurvature_connectedComponentMetric D]
    exact hsec _ _ _
  let : CompactSpace LW := e.toHomeomorph.compactSpace
  let : ConnectedSpace LW := e.surjective.connectedSpace e.contMDiff.continuous
  have hcLW : PoincareConjecture.MetricComplete gLW := by
    unfold PoincareConjecture.MetricComplete
    infer_instance
  have hdist := gL.edist_eq_of_diffeomorph_metric_pullback gLW e hmetric
  have hdiamW : ∀ x y : LW, gLW.edist x y ≤ 1 := by
    intro x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    exact (hdist x y).trans_le (hdiam x y)
  have hdistW (x y : W) : gW.edist x y = g.edist (x : M) (y : M) :=
    PoincareConjecture.RiemannianMetric.edist_subtype_val isClosed_connectedComponent
      g gW (fun _ _ _ => rfl) x y
  have hbufferW : ∀ x : LW, ∀ y : W,
      gW.edist (inclW x) y ≤ ENNReal.ofReal η → y ∈ V := by
    intro x y hy
    obtain ⟨x, rfl⟩ := e.surjective x
    rw [hdistW] at hy
    exact hbuffer x y hy
  let KW : LW → ℝ := K ∘ e.symm
  have hKW : Continuous KW := hK.comp e.symm.contMDiff.continuous
  have hKWnonneg : ∀ x, 0 ≤ KW x := fun x => hKnonneg (e.symm x)
  have hKWsec : ∀ x (v w : TangentSpace (𝓡 m) x),
      -KW x ≤ gLW.leviCivitaData.sectionalCurvature x v w := by
    have ht := gL.leviCivitaData.sectionalCurvature_lower_bound_of_metric_similarity
      gLW.leviCivitaData e (by norm_num : (0:ℝ) < 1)
      (fun x v w => by simpa only [one_mul] using (hmetric x v w).symm) hKsec
    intro x v w
    have ht' := ht x v w
    rw [inv_one, one_mul] at ht'
    exact ht'
  have hb := hbound W gW DW hcW hsecW fw hw hfw hhw V hunitW hpairW hcrossW
    htightW hhessW' hregW c (show CompactSpace LW from inferInstance)
    (show ConnectedSpace LW from inferInstance) hcLW hdiamW hbufferW
    KW hKW hKWnonneg hKWsec
  have hs := gL.leviCivitaData.integral_scalarCurvature_eq_of_diffeomorph
    gLW.leviCivitaData e hmetric (fun s => max 0 s)
  have hi : (∫ x, K x ∂gL.volumeMeasure) = ∫ y, KW y ∂gLW.volumeMeasure := by
    have ht := gL.integral_comp_equiv_volumeMeasure gLW e.toEquiv hdist KW
    exact ht
  change (∫ x, max 0 (gL.leviCivitaData.scalarCurvature x) ∂gL.volumeMeasure) ≤
    C * (1 + ∫ x, K x ∂gL.volumeMeasure)
  rw [hs, hi]
  exact hb
