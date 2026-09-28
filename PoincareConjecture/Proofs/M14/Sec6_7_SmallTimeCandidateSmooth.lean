import PoincareConjecture.Proofs.M14.Sec6_3_FamilyDensity
import PoincareConjecture.Proofs.M14.Mathlib.CompactPartialDerivative
import PoincareConjecture.Definitions.M14Exponential

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem smallTimeCandidate_family_smooth (E : M14ExponentialFamily G T x)
    {U : Set (G.Horizontal x)} {O : Set G.Point} {η : ℝ} (hη : 0 ≤ η)
    (hcapture : ∀ W ∈ U, ∀ σ ∈ Icc 0 η,
      (W, Real.sqrt σ) ∈ E.domain ∧ E.gamma W (Real.sqrt σ) ∈ O) :
    let metric := G.spacetime.horizontalMetric.toRiemannianMetric
    letI : NormedAddCommGroup (G.Horizontal x) :=
      (metric.toCore x).toNormedAddCommGroupOfTopology
        (metric.continuousAt x) (metric.isVonNBounded x)
    letI : InnerProductSpace ℝ (G.Horizontal x) :=
      .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, G.Horizontal x)) (spacetimeModel n) ∞
      (fun z : ℝ × G.Horizontal x => E.gamma z.2 z.1) (Icc 0 (Real.sqrt η) ×ˢ U) ∧
      ∀ W ∈ U, ∀ s ∈ Icc 0 (Real.sqrt η),
        (W, s) ∈ E.domain ∧ E.gamma W s ∈ O := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  have hmap (W : G.Horizontal x) (hW : W ∈ U) (s : ℝ)
      (hs : s ∈ Icc 0 (Real.sqrt η)) : (W, s) ∈ E.domain ∧ E.gamma W s ∈ O := by
    have hsη : s ^ 2 ≤ η := ((sq_le_sq₀ hs.1 (Real.sqrt_nonneg η)).mpr hs.2).trans_eq
      (Real.sq_sqrt hη)
    simpa only [Real.sqrt_sq hs.1] using hcapture W hW (s ^ 2) ⟨sq_nonneg s, hsη⟩
  have hE : ContMDiffOn ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ)))
      (spacetimeModel n) ∞ (fun z => E.gamma z.1 z.2) E.domain := E.family_smooth
  exact ⟨hE.comp (contMDiff_snd.prodMk contMDiff_fst).contMDiffOn
    (fun z hz => (hmap z.2 hz.2 z.1 hz.1).1), hmap⟩

theorem exists_smallTimeCandidate_coordinate_bound (E : M14ExponentialFamily G T x)
    (b : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b)
    {U K : Set (G.Horizontal x)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {O : Set G.Point} (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift O)
    {η : ℝ} (hη : 0 < η)
    (hcapture : ∀ W ∈ U, ∀ σ ∈ Icc 0 η,
      (W, Real.sqrt σ) ∈ E.domain ∧ E.gamma W (Real.sqrt σ) ∈ O) :
    let metric := G.spacetime.horizontalMetric.toRiemannianMetric
    letI : NormedAddCommGroup (G.Horizontal x) :=
      (metric.toCore x).toNormedAddCommGroupOfTopology
        (metric.continuousAt x) (metric.isVonNBounded x)
    letI : InnerProductSpace ℝ (G.Horizontal x) :=
      .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
    ContDiffOn ℝ ∞ (fun z : ℝ × G.Horizontal x => (lift (E.gamma z.2 z.1)).2.val)
      (Icc 0 (Real.sqrt η) ×ˢ U) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ W ∈ K, ∀ s ∈ Icc 0 (Real.sqrt η),
        ‖derivWithin (fun r => (lift (E.gamma W r)).2.val) (Icc 0 (Real.sqrt η)) s‖ ≤ M := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  obtain ⟨hγ, hmap⟩ := smallTimeCandidate_family_smooth E hη.le hcapture
  have hL := hlift.comp hγ (fun z hz => (hmap z.2 hz.2 z.1 hz.1).2)
  have hv : ContMDiff (𝓡 n) (𝓡 n) ∞
      (Subtype.val : G.gaugeCover.spatial b → EuclideanSpace ℝ (Fin n)) :=
    contMDiff_subtype_val
  have hcoord : ContDiffOn ℝ ∞
      (fun z : ℝ × G.Horizontal x => (lift (E.gamma z.2 z.1)).2.val)
      (Icc 0 (Real.sqrt η) ×ˢ U) := by
    have h := hv.comp_contMDiffOn (fun z hz => (hL z hz).snd)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    exact h.contDiffOn
  exact ⟨hcoord, hcoord.exists_uniform_derivWithin_bound_fst
    (uniqueDiffOn_Icc (Real.sqrt_pos.mpr hη)) isCompact_Icc hU hK hKU⟩

theorem exists_smallTimeCandidate_density_bound
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (E : M14ExponentialFamily G T x)
    {U K : Set (G.Horizontal x)} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {O : Set G.Point} {η : ℝ} (hη : 0 < η)
    (hcapture : ∀ W ∈ U, ∀ σ ∈ Icc 0 η,
      (W, Real.sqrt σ) ∈ E.domain ∧ E.gamma W (Real.sqrt σ) ∈ O) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ W ∈ K, ∀ s ∈ Icc 0 (Real.sqrt η),
      squareCurveDensity G (E.gamma W) (Icc 0 (Real.sqrt η)) s ≤ A := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  have hγ := (smallTimeCandidate_family_smooth E hη.le hcapture).1
  have hd := squareFamilyDensity_contDiffOn hM12
    (uniqueDiffOn_Icc (Real.sqrt_pos.mpr hη)) hU hγ
  obtain ⟨A, hA⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hd.continuousOn.mono (fun _ hz => ⟨hz.1, hKU hz.2⟩))
  refine ⟨max A 0, le_max_right _ _, ?_⟩
  intro W hW s hs
  have h := hA (s, W) ⟨hs, hW⟩
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans (le_max_left _ _))

end PoincareConjecture.M14
