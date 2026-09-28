import PoincareConjecture.Proofs.M14.Mathlib.OpenFirstPartialTangent
import PoincareConjecture.Proofs.M14.Sec6_3_InitialDifferential

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

theorem initialValueDifferential_contMDiffOn
    {U : Set (G.Horizontal x)} {C : Set ℝ} (hU : IsOpen U)
    (hC : UniqueDiffOn ℝ C)
    (hsm : M14HorizontalFamilySmooth G (initialValueCurve G T x) (U ×ˢ C))
    (W : G.Horizontal x) :
    let metric := G.spacetime.horizontalMetric.toRiemannianMetric
    letI : NormedAddCommGroup (G.Horizontal x) :=
      (metric.toCore x).toNormedAddCommGroupOfTopology
        (metric.continuousAt x) (metric.isVonNBounded x)
    letI : InnerProductSpace ℝ (G.Horizontal x) :=
      .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
    ContMDiffOn ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ)))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun z : G.Horizontal x × ℝ => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) (initialValueCurve G T x z.1 z.2)
          (initialValueDifferential G T x z.1 z.2 W)) (U ×ˢ C) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  have htan := hsm.contMDiffOn_partialTangent_fst_prod hU hC W (k := ∞) (by simp)
  have hproj : ContMDiff (spacetimeModel n).tangent
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) G.Point =>
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := G.Horizontal) v.proj
          (G.spacetime.horizontalProjection v.proj v.2)) :=
    G.spacetime.horizontalProjection_smooth
  exact hproj.comp_contMDiffOn htan

theorem initialValueDifferential_field_contMDiffOn
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hbase : G.spacetime.timeFunction x = T) {Z : G.Horizontal x} {s : ℝ}
    (hs : 0 < s) (hsurv : (Z, s) ∈ initialValueDomain G T x) (W : G.Horizontal x) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun r => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) (initialValueCurve G T x Z r)
          (initialValueDifferential G T x Z r W)) (Icc 0 s) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  obtain ⟨U, hU, hZU, _, hsm⟩ :=
    initialValueCurve_smooth_prefix hM04 hM12 hbase hs hsurv
  exact (initialValueDifferential_contMDiffOn hU (uniqueDiffOn_Icc hs) hsm W).comp
    ((contMDiff_const (c := Z)).prodMk contMDiff_id).contMDiffOn (fun _ hr => ⟨hZU, hr⟩)

end PoincareConjecture.M14
