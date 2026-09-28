import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalAffineSystem

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal
open Poincare.Analysis.Sobolev.Weak

noncomputable section

namespace PoincareConjecture.M60

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
private abbrev Jet (n : ℕ) := E (3 * n)
private abbrev Grad (n : ℕ) := E n × E n
private abbrev Base (n : ℕ) := LoopPlane × E n
private abbrev Point (n : ℕ) := Base n × Grad n

local instance jetSystemBilinearNormedGroup {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance jetSystemBilinearNormedSpace {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance jetSystemTrilinearNormedGroup {n : ℕ} :
    NormedAddCommGroup (E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance jetSystemTrilinearNormedSpace {n : ℕ} :
    NormedSpace ℝ (E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance jetSystemPairDualNormedGroup {n : ℕ} :
    NormedAddCommGroup (Grad n →L[ℝ] E n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance jetSystemPairDualNormedSpace {n : ℕ} :
    NormedSpace ℝ (Grad n →L[ℝ] E n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

local instance jetSystemPairDerivativeNormedGroup {n : ℕ} :
    NormedAddCommGroup (Grad n →L[ℝ] Grad n →L[ℝ] E n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance jetSystemPairDerivativeNormedSpace {n : ℕ} :
    NormedSpace ℝ (Grad n →L[ℝ] Grad n →L[ℝ] E n →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def suAlphaFirstJetPoint {n : ℕ} (z : LoopPlane × Jet n) : Point n :=
  ((z.1, suJetBlock (0 : Fin 3) z.2),
    (suJetBlock (1 : Fin 3) z.2, suJetBlock (2 : Fin 3) z.2))

def suAlphaJetOriginalFlux {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (p : Point n) : Grad n →L[ℝ] ℝ :=
  suAlphaCoordinateFlux g b alpha p.1 p.2

def suAlphaJetOriginalSource {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (p : Point n) : E n →L[ℝ] ℝ :=
  suAlphaCoordinateSource g b alpha p.1 p.2

def suAlphaFirstJetPrincipal {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (z : LoopPlane × Jet n) :
    Grad (3 * n) →L[ℝ] Grad (3 * n) →L[ℝ] ℝ :=
  let p := suAlphaFirstJetPoint z
  suJetBlockPrincipal (k := 3) (fderiv ℝ (suAlphaCoordinateFlux g b alpha p.1) p.2)

def suAlphaFirstJetFluxOffset {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (z : LoopPlane × Jet n) :
    Grad (3 * n) →L[ℝ] ℝ :=
  let p := suAlphaFirstJetPoint z
  let A := fderiv ℝ (suAlphaCoordinateFlux g b alpha p.1) p.2
  ((suAlphaJetOriginalFlux g b alpha p - A p.2).comp
    ((suJetBlock (0 : Fin 3)).prodMap (suJetBlock (0 : Fin 3)))) +
    ∑ k : Fin 2, (fderiv ℝ (suAlphaJetOriginalFlux g b alpha) p
      ((EuclideanSpace.single k 1, suJetBlock k.succ z.2), 0)).comp
        ((suJetBlock k.succ).prodMap (suJetBlock k.succ))

def suAlphaFirstJetSourceLinear {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (z : LoopPlane × Jet n) :
    Grad (3 * n) →L[ℝ] Jet n →L[ℝ] ℝ :=
  let p := suAlphaFirstJetPoint z
  ∑ k : Fin 2,
    ((ContinuousLinearMap.compL ℝ (Jet n) (E n) ℝ).flip (suJetBlock k.succ)).comp
      ((fderiv ℝ (suAlphaJetOriginalSource g b alpha) p).comp
        ((ContinuousLinearMap.inr ℝ (Base n) (Grad n)).comp
          ((suJetBlock k.succ).prodMap (suJetBlock k.succ))))

def suAlphaFirstJetSourceOffset {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (z : LoopPlane × Jet n) :
    Jet n →L[ℝ] ℝ :=
  let p := suAlphaFirstJetPoint z
  (suAlphaJetOriginalSource g b alpha p).comp (suJetBlock (0 : Fin 3)) +
    ∑ k : Fin 2, (fderiv ℝ (suAlphaJetOriginalSource g b alpha) p
      ((EuclideanSpace.single k 1, suJetBlock k.succ z.2), 0)).comp (suJetBlock k.succ)

def suAlphaFirstJetFlux {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (z : LoopPlane × Jet n)
    (q : Grad (3 * n)) : Grad (3 * n) →L[ℝ] ℝ :=
  suAlphaFirstJetPrincipal g b alpha z q + suAlphaFirstJetFluxOffset g b alpha z

def suAlphaFirstJetSource {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (z : LoopPlane × Jet n)
    (q : Grad (3 * n)) : Jet n →L[ℝ] ℝ :=
  suAlphaFirstJetSourceLinear g b alpha z q + suAlphaFirstJetSourceOffset g b alpha z

theorem suJetBlock_firstJet_zero {m : ℕ} (u : LoopPlane → E m) (x : LoopPlane) :
    suJetBlock (0 : Fin 3) (suFirstJet u x) = u x := by
  ext a
  change suFirstJet u x (finProdFinEquiv ((0 : Fin 3), a)) = u x a
  dsimp only [suFirstJet]
  simp only [Equiv.symm_apply_apply, Fin.cases_zero]

theorem suJetBlock_firstJet_succ {m : ℕ} (u : LoopPlane → E m) (k : Fin 2) (x : LoopPlane) :
    suJetBlock k.succ (suFirstJet u x) = fderiv ℝ u x (EuclideanSpace.single k 1) := by
  ext a
  change suFirstJet u x (finProdFinEquiv (k.succ, a)) = _
  dsimp only [suFirstJet]
  simp only [Equiv.symm_apply_apply, Fin.cases_succ]

theorem suJetBlock_firstJetWeakColumn_zero {m : ℕ}
    (V : Fin 2 → LoopPlane → E m) (H : Fin 2 → Fin 2 → LoopPlane → E m)
    (i : Fin 2) (x : LoopPlane) :
    suJetBlock (0 : Fin 3) (suFirstJetWeakColumn V H i x) = V i x := by
  ext a
  change suFirstJetWeakColumn V H i x (finProdFinEquiv ((0 : Fin 3), a)) = V i x a
  dsimp only [suFirstJetWeakColumn]
  simp only [Equiv.symm_apply_apply, Fin.cases_zero]

theorem suJetBlock_firstJetWeakColumn_succ {m : ℕ}
    (V : Fin 2 → LoopPlane → E m) (H : Fin 2 → Fin 2 → LoopPlane → E m)
    (i k : Fin 2) (x : LoopPlane) :
    suJetBlock k.succ (suFirstJetWeakColumn V H i x) = H k i x := by
  ext a
  change suFirstJetWeakColumn V H i x (finProdFinEquiv (k.succ, a)) = H k i x a
  dsimp only [suFirstJetWeakColumn]
  simp only [Equiv.symm_apply_apply, Fin.cases_succ]

theorem suAlphaJetOriginal_contDiffAt
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (p : Point n)
    (hy : p.1.2 ∈ (extChartAt (𝓡 n) b).target) :
    ContDiffAt ℝ ∞ (suAlphaJetOriginalFlux g b alpha) p ∧
      ContDiffAt ℝ ∞ (suAlphaJetOriginalSource g b alpha) p := by
  let G := g.pullbackCoefficients (chartAt (E n) b).symm
  let B (z : Point n) := (suAlphaRoundFactor z.1.1)⁻¹ • suAlphaPairMetric (G z.1.2)
  let D (z : Point n) := suAlphaPairMetricDerivative (fderiv ℝ G z.1.2)
  have hlambda (x : LoopPlane) : 0 < suAlphaRoundFactor x := by
    dsimp [suAlphaRoundFactor]
    positivity
  have hls : ContDiff ℝ ∞ suAlphaRoundFactor := by
    unfold suAlphaRoundFactor
    exact contDiff_const.div (((contDiff_norm_sq ℝ).add contDiff_const).pow 2)
      (fun x => by positivity)
  have hG : ContDiffOn ℝ ∞ G (extChartAt (𝓡 n) b).target := g.contDiffOn_chartCoefficients b
  have hDG : ContDiffOn ℝ ∞ (fderiv ℝ G) (extChartAt (𝓡 n) b).target :=
    hG.fderiv_of_isOpen (isOpen_extChartAt_target b) (by simp)
  have hPair := (suAlphaPairMetric_contDiffOn hG).contDiffAt
    ((isOpen_extChartAt_target b).mem_nhds hy)
  have hPairD := (suAlphaPairMetricDerivative_contDiffOn hDG).contDiffAt
    ((isOpen_extChartAt_target b).mem_nhds hy)
  have hB : ContDiffAt ℝ ∞ B p :=
    ((hls.contDiffAt.inv (hlambda p.1.1).ne').comp p contDiffAt_fst.fst).smul
      (hPair.comp p contDiffAt_fst.snd)
  have hD : ContDiffAt ℝ ∞ D p := hPairD.comp p contDiffAt_fst.snd
  obtain ⟨kappa, _, hkappa, _, _, _, hmetric⟩ := suAlpha_coordinate_metric_bounds g b
    (K := {p.1.2}) isCompact_singleton (by simpa only [singleton_subset_iff] using hy)
  have hnonneg (v : E n) : 0 ≤ G p.1.2 v v :=
    (mul_nonneg hkappa.le (sq_nonneg _)).trans (hmetric p.1.2 (mem_singleton _) v)
  have hpos : 0 < 1 + B p p.2 p.2 := by
    change 0 < 1 + (suAlphaRoundFactor p.1.1)⁻¹ *
      (G p.1.2 p.2.1 p.2.1 + G p.1.2 p.2.2 p.2.2)
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (inv_nonneg.mpr (hlambda p.1.1).le) (add_nonneg (hnonneg _) (hnonneg _)))
  have hbase : ContDiffAt ℝ ∞ (fun z : Point n => 1 + B z z.2 z.2) p := by fun_prop
  have hweight := hbase.rpow_const_of_ne (p := alpha - 1) hpos.ne'
  refine ⟨?_, ?_⟩
  · exact (hls.contDiffAt.comp p (by fun_prop)).smul
      ((contDiffAt_const.mul hweight).smul (hB.clm_apply (by fun_prop)))
  · exact (contDiffAt_const.mul hweight).smul
      ((hD.clm_apply (by fun_prop)).clm_apply (by fun_prop))

theorem suAlphaFirstJetPoint_contDiff {n : ℕ} : ContDiff ℝ ∞ (@suAlphaFirstJetPoint n) := by
  unfold suAlphaFirstJetPoint
  fun_prop

theorem suAlphaFirstJet_gradient_contDiffAt
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (z : LoopPlane × Jet n)
    (hy : suJetBlock (0 : Fin 3) z.2 ∈ (extChartAt (𝓡 n) b).target) :
    ContDiffAt ℝ ∞ (fun w : LoopPlane × Jet n =>
      fderiv ℝ (suAlphaCoordinateFlux g b alpha (suAlphaFirstJetPoint w).1)
        (suAlphaFirstJetPoint w).2) z := by
  apply ContDiffAt.fderiv (f := fun w =>
    suAlphaCoordinateFlux g b alpha (suAlphaFirstJetPoint w).1)
    (g := fun w => (suAlphaFirstJetPoint w).2)
  · have hF := (suAlphaJetOriginal_contDiffAt g b alpha (suAlphaFirstJetPoint z) hy).1
    exact hF.comp (z, (suAlphaFirstJetPoint z).2)
      ((suAlphaFirstJetPoint_contDiff.contDiffAt.comp _ contDiffAt_fst).fst.prodMk contDiffAt_snd)
  · exact suAlphaFirstJetPoint_contDiff.contDiffAt.snd
  · simp

theorem suJetBlockPrincipal_contDiff {k m : ℕ} :
    ContDiff ℝ ∞ (@suJetBlockPrincipal k m) := by
  classical
  let L : (Grad m →L[ℝ] Grad m →L[ℝ] ℝ) →ₗ[ℝ]
      (Grad (k * m) →L[ℝ] Grad (k * m) →L[ℝ] ℝ) := {
    toFun := suJetBlockPrincipal
    map_add' := by
      intro A B
      apply ContinuousLinearMap.ext
      intro v
      apply ContinuousLinearMap.ext
      intro w
      simp [suJetBlockPrincipal, ContinuousLinearMap.bilinearComp_apply, Finset.sum_add_distrib]
    map_smul' := by
      intro c A
      apply ContinuousLinearMap.ext
      intro v
      apply ContinuousLinearMap.ext
      intro w
      simp [suJetBlockPrincipal, ContinuousLinearMap.bilinearComp_apply, Finset.mul_sum]
  }
  exact L.toContinuousLinearMap.contDiff

theorem suAlphaFirstJet_coefficients_contDiffAt
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (z : LoopPlane × Jet n)
    (hy : suJetBlock (0 : Fin 3) z.2 ∈ (extChartAt (𝓡 n) b).target) :
    ContDiffAt ℝ ∞ (suAlphaFirstJetPrincipal g b alpha) z ∧
      ContDiffAt ℝ ∞ (suAlphaFirstJetFluxOffset g b alpha) z ∧
      ContDiffAt ℝ ∞ (suAlphaFirstJetSourceLinear g b alpha) z ∧
      ContDiffAt ℝ ∞ (suAlphaFirstJetSourceOffset g b alpha) z := by
  classical
  have hp := (@suAlphaFirstJetPoint_contDiff n).contDiffAt (x := z)
  have hO := suAlphaJetOriginal_contDiffAt g b alpha (suAlphaFirstJetPoint z) hy
  have hF := hO.1.comp z hp
  have hB := hO.2.comp z hp
  have hDF := (hO.1.fderiv_right (m := ∞) (by simp)).comp z hp
  have hDB := (hO.2.fderiv_right (m := ∞) (by simp)).comp z hp
  have hA := suAlphaFirstJet_gradient_contDiffAt g b alpha z hy
  refine ⟨suJetBlockPrincipal_contDiff.contDiffAt.comp z hA, ?_, ?_, ?_⟩
  · unfold suAlphaFirstJetFluxOffset
    dsimp only
    apply ContDiffAt.add
    · exact (hF.sub (hA.clm_apply hp.snd)).clm_comp contDiffAt_const
    · apply ContDiffAt.sum
      intro k _
      exact (hDF.clm_apply
        ((contDiffAt_const.prodMk ((suJetBlock k.succ).contDiff.contDiffAt.comp z
          contDiffAt_snd)).prodMk
          contDiffAt_const)).clm_comp contDiffAt_const
  · unfold suAlphaFirstJetSourceLinear
    dsimp only
    apply ContDiffAt.sum
    intro k _
    exact contDiffAt_const.clm_comp (hDB.clm_comp contDiffAt_const)
  · unfold suAlphaFirstJetSourceOffset
    dsimp only
    apply ContDiffAt.add
    · exact hB.clm_comp contDiffAt_const
    · apply ContDiffAt.sum
      intro k _
      exact (hDB.clm_apply
        ((contDiffAt_const.prodMk ((suJetBlock k.succ).contDiff.contDiffAt.comp z
          contDiffAt_snd)).prodMk
          contDiffAt_const)).clm_comp contDiffAt_const

def suAlphaFirstJetCoefficients
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) : SUAffineJetCoefficients (3 * n) where
  principal := suAlphaFirstJetPrincipal g b alpha
  fluxOffset := suAlphaFirstJetFluxOffset g b alpha
  sourceLinear := suAlphaFirstJetSourceLinear g b alpha
  sourceOffset := suAlphaFirstJetSourceOffset g b alpha

theorem suJetBlock_single {k m : ℕ} (j l : Fin k) (a : Fin m) :
    suJetBlock j (EuclideanSpace.single (finProdFinEquiv (l, a)) 1) =
      if j = l then EuclideanSpace.single a 1 else 0 := by
  classical
  ext c
  change EuclideanSpace.single (finProdFinEquiv (l, a)) (1 : ℝ)
    (finProdFinEquiv (j, c)) = _
  by_cases hj : j = l
  · subst j
    simp [finProdFinEquiv.injective.eq_iff]
  · simp [hj, finProdFinEquiv.injective.eq_iff]

theorem suJetBlock_columnBasis {k m : ℕ} (j l : Fin k) (a : Fin m) (i : Fin 2) :
    ((suJetBlock j).prodMap (suJetBlock j)) (suColumnBasis (finProdFinEquiv (l, a)) i) =
      if j = l then suColumnBasis a i else 0 := by
  classical
  by_cases hi : i = 0 <;> by_cases hj : j = l <;>
    simp [suColumnBasis, hi, hj, suJetBlock_single]

theorem suAlphaFirstJetPoint_fderiv {n : ℕ} (z w : LoopPlane × Jet n) :
    fderiv ℝ (@suAlphaFirstJetPoint n) z w = suAlphaFirstJetPoint w := by
  let P := ContinuousLinearMap.snd ℝ LoopPlane (Jet n)
  let L : (LoopPlane × Jet n) →L[ℝ] Point n :=
    ((ContinuousLinearMap.fst ℝ LoopPlane (Jet n)).prod
      ((suJetBlock (0 : Fin 3)).comp P)).prod
        (((suJetBlock (1 : Fin 3)).comp P).prod ((suJetBlock (2 : Fin 3)).comp P))
  change fderiv ℝ L z w = L w
  rw [L.fderiv]

theorem suAlphaFirstJet_flux_zero
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ)
    (z : LoopPlane × Jet n) (q : Grad (3 * n))
    (hq : ((suJetBlock (0 : Fin 3)).prodMap (suJetBlock (0 : Fin 3))) q =
      (suAlphaFirstJetPoint z).2) (a : Fin n) (i : Fin 2) :
    suAlphaFirstJetFlux g b alpha z q (suColumnBasis (finProdFinEquiv ((0 : Fin 3), a)) i) =
      suAlphaJetOriginalFlux g b alpha (suAlphaFirstJetPoint z) (suColumnBasis a i) := by
  classical
  simp only [suAlphaFirstJetFlux, suAlphaFirstJetPrincipal, suJetBlockPrincipal,
    sum_apply, ContinuousLinearMap.bilinearComp_apply, add_apply, sub_apply,
    suAlphaFirstJetFluxOffset, ContinuousLinearMap.comp_apply, suJetBlock_columnBasis]
  simp only [Fin.sum_univ_succ, Fin.succ_ne_zero, ↓reduceIte, map_zero, hq]
  ring

theorem suAlphaFirstJet_source_zero
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ)
    (z : LoopPlane × Jet n) (q : Grad (3 * n)) (a : Fin n) :
    suAlphaFirstJetSource g b alpha z q (EuclideanSpace.single (finProdFinEquiv
      ((0 : Fin 3), a)) 1) =
      suAlphaJetOriginalSource g b alpha (suAlphaFirstJetPoint z) (EuclideanSpace.single a 1) := by
  classical
  simp [suAlphaFirstJetSource, suAlphaFirstJetSourceLinear, suAlphaFirstJetSourceOffset,
    suJetBlock_single, ContinuousLinearMap.compL_apply]

theorem suAlphaJetOriginalFlux_fderiv_snd
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ) (p : Point n)
    (hy : p.1.2 ∈ (extChartAt (𝓡 n) b).target) (v : Grad n) :
    fderiv ℝ (suAlphaJetOriginalFlux g b alpha) p (0, v) =
      fderiv ℝ (suAlphaCoordinateFlux g b alpha p.1) p.2 v := by
  have hF := (suAlphaJetOriginal_contDiffAt g b alpha p hy).1.differentiableAt (by simp)
  have hi : HasFDerivAt (fun q : Grad n => (p.1, q))
      (ContinuousLinearMap.inr ℝ (Base n) (Grad n)) p.2 :=
    (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hd := hF.hasFDerivAt.comp p.2 hi
  have he := hd.fderiv
  exact (congrArg (fun L => L v) he).symm

theorem suAlphaFirstJet_flux_succ
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ)
    (z : LoopPlane × Jet n) (q : Grad (3 * n))
    (hy : suJetBlock (0 : Fin 3) z.2 ∈ (extChartAt (𝓡 n) b).target)
    (k : Fin 2) (a : Fin n) (i : Fin 2) :
    suAlphaFirstJetFlux g b alpha z q (suColumnBasis (finProdFinEquiv (k.succ, a)) i) =
      fderiv ℝ (suAlphaJetOriginalFlux g b alpha) (suAlphaFirstJetPoint z)
        ((EuclideanSpace.single k 1, suJetBlock k.succ z.2),
          ((suJetBlock k.succ).prodMap (suJetBlock k.succ)) q) (suColumnBasis a i) := by
  classical
  have hsum : ((EuclideanSpace.single k (1 : ℝ), suJetBlock k.succ z.2),
      ((suJetBlock k.succ).prodMap (suJetBlock k.succ)) q) =
      ((0 : Base n), ((suJetBlock k.succ).prodMap (suJetBlock k.succ)) q) +
        ((EuclideanSpace.single k (1 : ℝ), suJetBlock k.succ z.2), (0 : Grad n)) := by simp
  rw [hsum, map_add, add_apply,
    suAlphaJetOriginalFlux_fderiv_snd g b alpha _ hy]
  fin_cases k <;> simp [suAlphaFirstJetFlux, suAlphaFirstJetPrincipal, suJetBlockPrincipal,
    suAlphaFirstJetFluxOffset, ContinuousLinearMap.bilinearComp_apply,
    suJetBlock_columnBasis, Fin.sum_univ_succ]

theorem suAlphaFirstJet_source_succ
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) (alpha : ℝ)
    (z : LoopPlane × Jet n) (q : Grad (3 * n)) (k : Fin 2) (a : Fin n) :
    suAlphaFirstJetSource g b alpha z q (EuclideanSpace.single (finProdFinEquiv (k.succ, a)) 1) =
      fderiv ℝ (suAlphaJetOriginalSource g b alpha) (suAlphaFirstJetPoint z)
        ((EuclideanSpace.single k 1, suJetBlock k.succ z.2),
          ((suJetBlock k.succ).prodMap (suJetBlock k.succ)) q) (EuclideanSpace.single a 1) := by
  classical
  have hsum : ((EuclideanSpace.single k (1 : ℝ), suJetBlock k.succ z.2),
      ((suJetBlock k.succ).prodMap (suJetBlock k.succ)) q) =
      ((0 : Base n), ((suJetBlock k.succ).prodMap (suJetBlock k.succ)) q) +
        ((EuclideanSpace.single k (1 : ℝ), suJetBlock k.succ z.2), (0 : Grad n)) := by simp
  rw [hsum, map_add, add_apply]
  fin_cases k <;> simp [suAlphaFirstJetSource, suAlphaFirstJetSourceLinear,
    suAlphaFirstJetSourceOffset, suJetBlock_single, ContinuousLinearMap.compL_apply]

end PoincareConjecture.M60
