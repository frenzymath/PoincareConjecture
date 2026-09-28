import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Graph.Component
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.MetricExpansion.Global
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.Transport.Diffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.AreaConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Diffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Immersion

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
open Set Function Filter TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold

private theorem contMDiff_lift_of_injective_localDiffeomorph
    {n : ℕ} {N P L : Type*} [TopologicalSpace N] [TopologicalSpace P] [TopologicalSpace L]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) L]
    {F : N → L} {G : P → L} {e : N → P}
    (hF : ContMDiff (𝓡 n) (𝓡 n) ∞ F)
    (hG : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ G) (hGi : Injective G)
    (he : ∀ x, G (e x) = F x) : ContMDiff (𝓡 n) (𝓡 n) ∞ e := by
  intro x
  have hloc := hG (e x)
  have hi : ContMDiffAt (𝓡 n) (𝓡 n) ∞ hloc.localInverse (F x) := by
    rw [← he x]
    exact hloc.localInverse_contMDiffAt
  apply (hi.comp x (hF x)).congr_of_eventuallyEq
  have hn := hloc.localInverse_eventuallyEq_right
  rw [he x] at hn
  filter_upwards [(hF x).continuousAt.tendsto.eventually hn] with y hy
  apply hGi
  exact (he y).trans hy.symm

theorem exists_diffeomorph_of_injective_localDiffeomorph_same_range
    {n : ℕ} {N P L : Type*} [TopologicalSpace N] [TopologicalSpace P] [TopologicalSpace L]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) L]
    {F : N → L} {G : P → L}
    (hF : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ F)
    (hG : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ G)
    (hFi : Injective F) (hGi : Injective G) (hrange : range F = range G) :
    ∃ e : N ≃ₘ⟮𝓡 n, 𝓡 n⟯ P, ∀ x, G (e x) = F x := by
  classical
  have hpre (x : N) : ∃ y : P, G y = F x := by
    apply mem_range.mp
    rw [← hrange]
    exact mem_range_self x
  choose e he using hpre
  have hbij : Bijective e := by
    constructor
    · intro x y hxy
      apply hFi
      rw [← he x, ← he y, hxy]
    · intro y
      have hy : G y ∈ range F := hrange ▸ mem_range_self y
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, hGi ((he x).trans hx)⟩
  let E := Equiv.ofBijective e hbij
  have hEs : ContMDiff (𝓡 n) (𝓡 n) ∞ E :=
    contMDiff_lift_of_injective_localDiffeomorph hF.contMDiff hG hGi he
  have hEinv : ∀ y, F (E.symm y) = G y := by
    intro y
    rw [← he (E.symm y)]
    exact congrArg G (E.apply_symm_apply y)
  exact ⟨{ E with
    contMDiff_toFun := hEs
    contMDiff_invFun := contMDiff_lift_of_injective_localDiffeomorph
      hG.contMDiff hF hFi hEinv }, he⟩

private theorem range_eq_component_of_compact_localDiffeomorph
    {n : ℕ} {N L : Type*} [TopologicalSpace N] [TopologicalSpace L]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) L]
    [CompactSpace N] [ConnectedSpace N] [T2Space L]
    {F : N → L} (hF : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ F) (x : N) :
    range F = connectedComponent (F x) := by
  have hc := hF.contMDiff.continuous
  have hclopen : IsClopen (range F) := ⟨(isCompact_range hc).isClosed, hF.isOpen_range⟩
  exact (isPreconnected_range hc).subset_connectedComponent (mem_range_self x)
    |>.antisymm (hclopen.connectedComponent_subset (mem_range_self x))

end Poincare.Manifold

namespace PoincareConjecture.RiemannianMetric

theorem area_le_of_diffeomorph_expands_metric
    {N P : Type*} [TopologicalSpace N] [TopologicalSpace P] [T3Space N] [T3Space P]
    [MeasurableSpace N] [BorelSpace N] [MeasurableSpace P] [BorelSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) P]
    [IsManifold (𝓡 2) ∞ N] [IsManifold (𝓡 2) ∞ P] [CompactSpace N] [CompactSpace P]
    (gN : RiemannianMetric 2 N) (gP : RiemannianMetric 2 P)
    (e : N ≃ₘ⟮𝓡 2, 𝓡 2⟯ P)
    (hmetric : ∀ x (v : TangentSpace (𝓡 2) x), gN.inner x v v ≤
      gP.inner (e x) (mfderiv (𝓡 2) (𝓡 2) e x v) (mfderiv (𝓡 2) (𝓡 2) e x v)) :
    gN.volumeMeasure.real univ ≤ gP.volumeMeasure.real univ := by
  let h : RiemannianMetric 2 N := Induced.pullbackMetric gP e e.contMDiff
    (fun x => (e.isLocalDiffeomorph x).mfderivToContinuousLinearEquiv (by simp) |>.injective)
  have harea := h.area_le_of_quadraticForm_le gN (by norm_num : (0 : ℝ) < 1)
    (fun x v => by
      change gN.inner x v v ≤ 1 * gP.inner (e x)
        (mfderiv (𝓡 2) (𝓡 2) e x v) (mfderiv (𝓡 2) (𝓡 2) e x v)
      simpa only [one_mul] using hmetric x v)
  have hvol := volumeMeasure_image_diffeomorph h gP e (fun _ _ _ => rfl) univ
  have heuniv : (e : N → P) '' univ = univ :=
    image_univ_of_surjective (show Surjective (e : N → P) from e.surjective)
  rw [heuniv] at hvol
  simpa only [one_mul, Measure.real, ← hvol] using harea

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.LeviCivitaData

variable {M N P : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [T2Space M] [T3Space N] [T3Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) P]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 2) ∞ N] [IsManifold (𝓡 2) ∞ P]
  [CompactSpace N] [ConnectedSpace N] [CompactSpace P] [ConnectedSpace P]
  {g : RiemannianMetric 3 M}

omit [T3Space N] [T3Space P] in

theorem exists_diffeomorph_between_transported_level_parametrizations
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, a < f y → 1 ≤ g.inner y (D.gradient f y) (D.gradient f y))
    {Φ : ℝ → M → M} (h0 : ∀ x, Φ 0 x = x)
    (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x) (D.boundedNormalizedGradient f))
    (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (Function.uncurry Φ))
    {c d : ℝ} (hc : a < c) (hd : a < d)
    (F : N → openLevelSet f (g.regularDomain hf) c)
    (G : P → openLevelSet f (g.regularDomain hf) d)
    (hF : ContMDiff (𝓡 2) (𝓡 3) ∞ (openLevelIncl f (g.regularDomain hf) c ∘ F))
    (hG : ContMDiff (𝓡 2) (𝓡 3) ∞ (openLevelIncl f (g.regularDomain hf) d ∘ G))
    (hFi : Injective F) (hGi : Injective G)
    (hFd : ∀ x, Injective (mfderiv (𝓡 2) (𝓡 3)
      (openLevelIncl f (g.regularDomain hf) c ∘ F) x))
    (hGd : ∀ x, Injective (mfderiv (𝓡 2) (𝓡 3)
      (openLevelIncl f (g.regularDomain hf) d ∘ G) x))
    (x₀ : N) (y₀ : P)
    (hbase : Φ (d - c) (openLevelIncl f (g.regularDomain hf) c (F x₀)) =
      openLevelIncl f (g.regularDomain hf) d (G y₀)) :
    ∃ e : N ≃ₘ⟮𝓡 2, 𝓡 2⟯ P, ∀ x,
      openLevelIncl f (g.regularDomain hf) d (G (e x)) =
        Φ (d - c) (openLevelIncl f (g.regularDomain hf) c (F x)) := by
  let U := g.regularDomain hf
  let hreg := g.regularDomain_regular hf
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf U hreg 2 c
  let := openLevelSetChartedSpace hf U hreg 2 d
  let := isManifold_openLevelSet hf U hreg 2 c
  let := isManifold_openLevelSet hf U hreg 2 d
  obtain ⟨eL, heL⟩ := D.exists_normalizedGradient_levelDiffeomorph hf ha h0 hΦ hadd hs hc hd
  have hFl := Poincare.Manifold.isLocalDiffeomorph_into_level_of_ambient_immersion
    hf U hreg c F hF hFd
  have hGl := Poincare.Manifold.isLocalDiffeomorph_into_level_of_ambient_immersion
    hf U hreg d G hG hGd
  have hFt : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (eL ∘ F) :=
    fun x => (hFl x).comp (𝓡 2) (openLevelSet f U d) (eL.isLocalDiffeomorph (F x))
  have hbase' : eL (F x₀) = G y₀ := by
    apply (isEmbedding_openLevelIncl f U d).injective
    exact (heL (F x₀)).trans hbase
  have hrange : range (eL ∘ F) = range G := by
    rw [Poincare.Manifold.range_eq_component_of_compact_localDiffeomorph hFt x₀,
      Poincare.Manifold.range_eq_component_of_compact_localDiffeomorph hGl y₀]
    exact congrArg connectedComponent hbase'
  obtain ⟨e, he⟩ := Poincare.Manifold.exists_diffeomorph_of_injective_localDiffeomorph_same_range
    hFt hGl (eL.injective.comp hFi) hGi hrange
  exact ⟨e, fun x => (congrArg (openLevelIncl f U d) (he x)).trans (heL (F x))⟩

theorem exists_area_nondecreasing_diffeomorph_between_transported_levels
    [MeasurableSpace N] [BorelSpace N] [MeasurableSpace P] [BorelSpace P]
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, a < f y → 1 ≤ g.inner y (D.gradient f y) (D.gradient f y))
    (hhess : ∀ y, a < f y → ∀ w : TangentSpace (𝓡 3) y,
      mvfderiv (𝓡 3) f y w = 0 → 0 ≤ D.hessian f y w w)
    {Φ : ℝ → M → M} (h0 : ∀ x, Φ 0 x = x)
    (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x) (D.boundedNormalizedGradient f))
    (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (Function.uncurry Φ))
    {c d : ℝ} (hc : a < c) (hcd : c ≤ d)
    (F : N → openLevelSet f (g.regularDomain hf) c)
    (G : P → openLevelSet f (g.regularDomain hf) d)
    (hF : ContMDiff (𝓡 2) (𝓡 3) ∞ (openLevelIncl f (g.regularDomain hf) c ∘ F))
    (hG : ContMDiff (𝓡 2) (𝓡 3) ∞ (openLevelIncl f (g.regularDomain hf) d ∘ G))
    (hFi : Injective F) (hGi : Injective G)
    (hFd : ∀ x, Injective (mfderiv (𝓡 2) (𝓡 3)
      (openLevelIncl f (g.regularDomain hf) c ∘ F) x))
    (hGd : ∀ x, Injective (mfderiv (𝓡 2) (𝓡 3)
      (openLevelIncl f (g.regularDomain hf) d ∘ G) x))
    (gN : RiemannianMetric 2 N) (gP : RiemannianMetric 2 P)
    (hN : ∀ x (v w : TangentSpace (𝓡 2) x), gN.inner x v w =
      g.inner (openLevelIncl f (g.regularDomain hf) c (F x))
        (mfderiv (𝓡 2) (𝓡 3) (openLevelIncl f (g.regularDomain hf) c ∘ F) x v)
        (mfderiv (𝓡 2) (𝓡 3) (openLevelIncl f (g.regularDomain hf) c ∘ F) x w))
    (hP : ∀ x (v w : TangentSpace (𝓡 2) x), gP.inner x v w =
      g.inner (openLevelIncl f (g.regularDomain hf) d (G x))
        (mfderiv (𝓡 2) (𝓡 3) (openLevelIncl f (g.regularDomain hf) d ∘ G) x v)
        (mfderiv (𝓡 2) (𝓡 3) (openLevelIncl f (g.regularDomain hf) d ∘ G) x w))
    (x₀ : N) (y₀ : P)
    (hbase : Φ (d - c) (openLevelIncl f (g.regularDomain hf) c (F x₀)) =
      openLevelIncl f (g.regularDomain hf) d (G y₀)) :
    ∃ e : N ≃ₘ⟮𝓡 2, 𝓡 2⟯ P,
      (∀ x, openLevelIncl f (g.regularDomain hf) d (G (e x)) =
        Φ (d - c) (openLevelIncl f (g.regularDomain hf) c (F x))) ∧
      (∀ x (v : TangentSpace (𝓡 2) x), gN.inner x v v ≤
        gP.inner (e x) (mfderiv (𝓡 2) (𝓡 2) e x v) (mfderiv (𝓡 2) (𝓡 2) e x v)) ∧
      gN.volumeMeasure.real univ ≤ gP.volumeMeasure.real univ := by
  obtain ⟨e, he⟩ := D.exists_diffeomorph_between_transported_level_parametrizations
    hf ha h0 hΦ hadd hs hc (hc.trans_le hcd) F G hF hG hFi hGi hFd hGd x₀ y₀ hbase
  let F₀ := openLevelIncl f (g.regularDomain hf) c ∘ F
  let G₀ := openLevelIncl f (g.regularDomain hf) d ∘ G
  have hFs : ContMDiff (𝓡 3) (𝓡 3) ∞ (Φ (d - c)) :=
    hs.comp (contMDiff_const.prodMk contMDiff_id)
  have hmetric (x : N) (v : TangentSpace (𝓡 2) x) : gN.inner x v v ≤
      gP.inner (e x) (mfderiv (𝓡 2) (𝓡 2) e x v) (mfderiv (𝓡 2) (𝓡 2) e x v) := by
    have hlevel : f ∘ F₀ = fun _ => c := funext (fun y => (F y).2)
    have htan : mvfderiv (𝓡 3) f (F₀ x) (mfderiv (𝓡 2) (𝓡 3) F₀ x v) = 0 := by
      have hd := mvfderiv_comp x ((hf _).mdifferentiableAt (by simp))
        ((hF x).mdifferentiableAt (by simp))
      rw [hlevel, mvfderiv_const] at hd
      exact (congrArg (fun L => L v) hd).symm
    have hexp := D.boundedNormalizedGradient_flow_expands_level_metric hf hs h0 hΦ ha hhess
      (show a < f (F₀ x) by rw [show f (F₀ x) = c from (F x).2]; exact hc)
      (mfderiv (𝓡 2) (𝓡 3) F₀ x v) htan (sub_nonneg.mpr hcd)
    have hcomp : G₀ ∘ e = Φ (d - c) ∘ F₀ := funext he
    have hd := mfderiv_comp x ((hFs _).mdifferentiableAt (by simp))
      ((hF x).mdifferentiableAt (by simp))
    rw [← hcomp, mfderiv_comp x ((hG _).mdifferentiableAt (by simp))
      ((e.contMDiff x).mdifferentiableAt (by simp))] at hd
    have hv := congrArg (fun L => L v) hd
    change mfderiv (𝓡 2) (𝓡 3) G₀ (e x) (mfderiv (𝓡 2) (𝓡 2) e x v) =
      mfderiv (𝓡 3) (𝓡 3) (Φ (d - c)) (F₀ x) (mfderiv (𝓡 2) (𝓡 3) F₀ x v) at hv
    have hpoint : G₀ (e x) = Φ (d - c) (F₀ x) := he x
    rw [hN, hP]
    change g.inner (F₀ x) (mfderiv (𝓡 2) (𝓡 3) F₀ x v)
      (mfderiv (𝓡 2) (𝓡 3) F₀ x v) ≤
      g.inner (G₀ (e x))
        (mfderiv (𝓡 2) (𝓡 3) G₀ (e x) (mfderiv (𝓡 2) (𝓡 2) e x v))
        (mfderiv (𝓡 2) (𝓡 3) G₀ (e x) (mfderiv (𝓡 2) (𝓡 2) e x v))
    rw [hv, hpoint]
    exact hexp
  exact ⟨e, he, hmetric, gN.area_le_of_diffeomorph_expands_metric gP e hmetric⟩

end PoincareConjecture.LeviCivitaData
