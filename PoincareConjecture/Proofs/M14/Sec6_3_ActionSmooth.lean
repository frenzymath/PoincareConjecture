import PoincareConjecture.Proofs.M14.Mathlib.ClosedFamilyPrimitive
import PoincareConjecture.Proofs.M14.Sec6_3_FamilyDensity
import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialCoherence
import PoincareConjecture.Proofs.M14.Sec6_3_MaximalSmooth
import PoincareConjecture.Proofs.M14.Sec6_1_SquareDensity












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

private theorem inner_heq {x y : G.Point} (h : x = y)
    {v : G.Horizontal x} {w : G.Horizontal y} (hv : HEq v w) :
    G.spacetime.horizontalMetric.inner x v v = G.spacetime.horizontalMetric.inner y w w := by
  cases h
  cases hv
  rfl




theorem initialValueAction_eq_density_primitive
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {Z : G.Horizontal x} {S r : ℝ} (hS : 0 < S)
    (hsurv : (Z, S) ∈ initialValueDomain G T x) (hr : r ∈ Icc 0 S) :
    initialValueAction G T x Z r =
      ∫ t in 0..r, squareCurveDensity G (initialValueCurve G T x Z) (Icc 0 S) t := by
  let P := selectedInitialValuePath ⟨hS, (initialValueDomain_positive_iff hS).mp hsurv⟩
  have hC : M14SqrtParameterInterval 0 (S ^ 2) = Icc 0 S := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hS.le]
  have heq : EqOn (initialValueCurve G T x Z) P.square_path.curve (Icc 0 S) := by
    simpa only [hC] using initialValueCurve_eqOn_square hM04 hM12 P
  rw [initialValueAction_eq_integral_prefix hM04 hM12 P
    (by simpa only [Real.sqrt_sq hS.le] using hr)]
  apply intervalIntegral.integral_congr_Ioo_of_le hr.1
  intro t ht
  have htC : t ∈ Icc 0 S := ⟨ht.1.le, ht.2.le.trans hr.2⟩
  have hv := projectedCurveVelocityWithin_congrOn (G := G) heq htC
  rw [squareRoot_projectedVelocityWithin_subset P.square_path
    (by rw [hC]) htC (uniqueDiffOn_Icc hS t htC)] at hv
  have hinner := inner_heq (heq htC) hv
  unfold squareRootLIntegrand squareCurveDensity
  rw [hinner, heq htC]




theorem initialValueAction_smooth_prefix
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {U : Set (G.Horizontal x)} {S : ℝ} (hU : IsOpen U) (hS : 0 < S)
    (hsurv : U ×ˢ Icc 0 S ⊆ initialValueDomain G T x)
    (hsm : M14HorizontalFamilySmooth G (initialValueCurve G T x) (U ×ˢ Icc 0 S)) :
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
    ContMDiffOn ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞
      (fun z => initialValueAction G T x z.1 z.2) (U ×ˢ Icc 0 S) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let : FiniteDimensional ℝ (G.Horizontal x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n)) G.Horizontal x
  have hγ₀ : ContMDiffOn ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ))) (spacetimeModel n) ∞
      (fun z : G.Horizontal x × ℝ => initialValueCurve G T x z.1 z.2) (U ×ˢ Icc 0 S) := hsm
  have hγ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, G.Horizontal x))) (spacetimeModel n) ∞
      (fun z : ℝ × G.Horizontal x => initialValueCurve G T x z.2 z.1) (Icc 0 S ×ˢ U) :=
    hγ₀.comp (contMDiff_snd.prodMk contMDiff_fst).contMDiffOn (fun _ hz => ⟨hz.2, hz.1⟩)
  have hd := squareFamilyDensity_contDiffOn hM12 (uniqueDiffOn_Icc hS) hU hγ
  have hp := closedFamilyPrimitive_contDiffOn hS hU _ hd
  have ha : ContDiffOn ℝ ∞ (fun z : G.Horizontal x × ℝ => initialValueAction G T x z.1 z.2)
      (U ×ˢ Icc 0 S) := by
    apply hp.congr
    intro z hz
    exact initialValueAction_eq_density_primitive hM04 hM12 hS
      (hsurv ⟨hz.1, hS.le, le_rfl⟩) hz.2
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact ha.contMDiffOn




theorem initialValueAction_smooth
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hbase : G.spacetime.timeFunction x = T) :
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
    ContMDiffOn ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞
      (fun z => initialValueAction G T x z.1 z.2)
      (initialValueDomain G T x ∩ {z | 0 < z.2}) := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  rintro ⟨Z, s⟩ ⟨hsurv, hpos⟩
  obtain ⟨S, hsS, U, hU, hZU, hnear, htube, hsm⟩ :=
    initialValueCurve_smooth_neighborhood_positive hM04 hM12 hbase hpos hsurv
  exact ((initialValueAction_smooth_prefix hM04 hM12 hU (hpos.trans_le hsS) htube hsm)
    (Z, s) ⟨hZU, hpos.le, hsS⟩).mono_of_mem_nhdsWithin
      (nhdsWithin_mono (Z, s) (fun _ hz => initialValueDomain_admissible hbase hz.1) hnear)




theorem exponentialFamily_action_smooth
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) :
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
    ContMDiffOn ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞
      (fun z => E.action z.1 z.2) (E.domain ∩ {z | 0 < z.2}) := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have h := initialValueAction_smooth hM04 hM12 E.base_time
  rw [← exponentialFamily_domain_eq E] at h
  exact h.congr (fun _ hz => exponentialFamily_action_eq hM04 hM12 E hz.1 hz.2)

end PoincareConjecture.M14
