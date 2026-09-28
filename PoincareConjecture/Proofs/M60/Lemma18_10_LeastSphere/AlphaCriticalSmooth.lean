import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalProlongation
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalJetMetric
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalHolder
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter Metric
open scoped ContDiff Topology ENNReal Manifold
open Poincare.Analysis.Sobolev.Weak

noncomputable section

namespace PoincareConjecture.M60

def SUQuadraticWeakSystem.restrict {m : ℕ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)} {center : LoopPlane} {R r : ℝ}
    (S : SUQuadraticWeakSystem u V center R) (hr : 0 < r) (hrR : r ≤ R) :
    SUQuadraticWeakSystem u V center r := by
  have hsub : ball center r ⊆ ball center R := ball_subset_ball hrR
  have hcsub : closedBall center r ⊆ closedBall center R := closedBall_subset_closedBall hrR
  have hprod : closedBall center r ×ˢ closedBall (u center) S.targetRadius ⊆
      closedBall center R ×ˢ closedBall (u center) S.targetRadius :=
    prod_mono hcsub Subset.rfl
  refine { S with
    radius_pos := hr
    coordinate_continuous := S.coordinate_continuous.mono hcsub
    coordinate_memLp := S.coordinate_memLp.mono_measure (Measure.restrict_mono hsub le_rfl)
    column_memLp := fun i => (S.column_memLp i).mono_measure (Measure.restrict_mono hsub le_rfl)
    weak_derivative := fun i a => (S.weak_derivative i a).restrict isOpen_ball hsub
    coordinate_range := S.coordinate_range.mono_left hcsub
    flux_continuous := S.flux_continuous.mono (prod_mono hprod Subset.rfl)
    source_continuous := S.source_continuous.mono (prod_mono hprod Subset.rfl)
    flux_bound := fun z hz q => S.flux_bound z (hprod hz) q
    source_bound := fun z hz q => S.source_bound z (hprod hz) q
    flux_monotone := fun z hz q w => S.flux_monotone z (hprod hz) q w
    flux_gradient_bound := fun z hz q w => S.flux_gradient_bound z (hprod hz) q w
    flux_base_bound := fun x hx y hy q => S.flux_base_bound x (hprod hx) y (hprod hy) q
    source_gradient_bound := fun z hz q w => S.source_gradient_bound z (hprod hz) q w
    source_base_bound := fun x hx y hy q => S.source_base_bound x (hprod hx) y (hprod hy) q
    flux_integrable := fun phi hp hpc hps =>
      (S.flux_integrable phi hp hpc (hps.trans hsub)).mono_set hsub
    source_integrable := fun phi hp hpc hps =>
      (S.source_integrable phi hp hpc (hps.trans hsub)).mono_set hsub
    equation := ?_ }
  intro phi hp hpc hps
  have he := S.equation phi hp hpc (hps.trans hsub)
  have hnot (x : LoopPlane) (hx : x ∉ ball center r) : x ∉ tsupport phi :=
    fun ht => hx (hps ht)
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hsub
      (fun x hx => by
        simp only [fderiv_of_notMem_tsupport (𝕜 := ℝ) (hnot x hx.2), zero_apply,
          Prod.mk_zero_zero, map_zero]),
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hsub
      (fun x hx => by rw [image_eq_zero_of_notMem_tsupport (hnot x hx.2), map_zero])] at he
  exact he

theorem suAffineWeakSystem_smooth_local :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (m : ℕ)
      {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
      {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)} {center : LoopPlane} {R : ℝ}
      (S : SUQuadraticWeakSystem u V center R) (C : SUAffineJetCoefficients m),
      S.flux = C.flux → S.source = C.source →
      ∀ {O : Set (LoopPlane × EuclideanSpace ℝ (Fin m))}, IsOpen O → (center, u center) ∈ O →
      ContDiffOn ℝ ∞ C.principal O → ContDiffOn ℝ ∞ C.fluxOffset O →
      ContDiffOn ℝ ∞ C.sourceLinear O → ContDiffOn ℝ ∞ C.sourceOffset O →
      ∀ {nu : ℝ}, 0 < nu →
      (∀ z ∈ O, ∀ q, nu * ‖q‖ ^ 2 ≤ C.principal z q q) →
      SUAffineJetNormalization C O delta → ContDiffAt ℝ ∞ u center := by
  obtain ⟨delta, hdelta, hfinite⟩ := suAffineWeakSystem_contDiff_finite
  refine ⟨delta, hdelta, ?_⟩
  intro m u V center R S C hflux hsource O hO hcenter hA hc hB hd nu hnu hcoercive N
  have hu : ContinuousAt u center :=
    S.coordinate_continuous.continuousAt (closedBall_mem_nhds center S.radius_pos)
  have hnear := (continuousAt_id.prodMk hu).preimage_mem_nhds (hO.mem_nhds hcenter)
  obtain ⟨s, hs, hsmall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  let r := min (s / 2) (R / 2)
  have hr : 0 < r := lt_min (half_pos hs) (half_pos S.radius_pos)
  have hrs : r ≤ s := (min_le_left _ _).trans (half_le_self hs.le)
  have hrR : r ≤ R := (min_le_right _ _).trans (half_le_self S.radius_pos.le)
  have hmap : MapsTo (fun x => (x, u x)) (closedBall center r) O :=
    fun x hx => hsmall (closedBall_subset_closedBall hrs hx)
  apply contDiffAt_infty.mpr
  intro k
  exact hfinite k m (S.restrict hr hrR) C hflux hsource hO hmap hA hc hB hd
    hnu hcoercive N

theorem suAlphaSphere_smooth_of_coordinates
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : C(UnitTwoSphere, M))
    (hcoord : ∀ p : UnitTwoSphere,
      ContDiffAt ℝ ∞ (suAlphaChartCoordinate (n := n) f p) ((chartAt LoopPlane p) p)) :
    ContMDiff (𝓡 2) (𝓡 n) ∞ f := by
  intro p
  let cs := chartAt LoopPlane p
  let ct := chartAt (EuclideanSpace ℝ (Fin n)) (f p)
  let u := suAlphaChartCoordinate (n := n) f p
  have hps : p ∈ cs.source := mem_chart_source LoopPlane p
  have hpt : f p ∈ ct.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) (f p)
  have hvalue : u (cs p) = ct (f p) := by
    change ct (f (cs.symm (cs p))) = ct (f p)
    rw [cs.left_inv hps]
  have hi : ContMDiffAt (𝓡 n) (𝓡 n) ∞ ct.symm (u (cs p)) := by
    rw [hvalue]
    exact contMDiffOn_chart_symm.contMDiffAt (ct.open_target.mem_nhds (ct.map_source hpt))
  have hs : ContMDiffAt (𝓡 2) (𝓡 2) ∞ cs p :=
    contMDiffOn_chart.contMDiffAt (cs.open_source.mem_nhds hps)
  have hu : ContMDiffAt (𝓡 2) (𝓡 n) ∞ u (cs p) :=
    contMDiffAt_iff_contDiffAt.mpr (hcoord p)
  apply ((hi.comp (cs p) hu).comp p hs).congr_of_eventuallyEq
  filter_upwards [cs.open_source.mem_nhds hps,
    f.continuous.continuousAt (ct.open_source.mem_nhds hpt)] with y hys hyt
  change f y = ct.symm (ct (f (cs.symm (cs y))))
  rw [cs.left_inv hys, ct.left_inv hyt]

theorem suWeakAlphaCoordinate_smooth_of_holder
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 / 32 ∧
      ∀ (b : M) (alpha : ℝ)
        (u : LoopPlane → EuclideanSpace ℝ (Fin n))
        (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n))
        (center : LoopPlane) (radius : ℝ),
        1 ≤ alpha → alpha ≤ 1 + eps0 →
        (S : SUWeakAlphaCoordinate g b alpha u V center radius) →
        (G : SUInitialGain u V center radius) →
        SUC1HolderGain u V center G.radius → ContDiffAt ℝ ∞ u center := by
  obtain ⟨delta, hdelta, hsmooth⟩ := suAffineWeakSystem_smooth_local
  let eps0 := min (1 / 32 : ℝ) (delta / 16)
  have heps : 0 < eps0 := lt_min (by norm_num) (div_pos hdelta (by norm_num))
  refine ⟨eps0, heps, min_le_left _ _, ?_⟩
  intro b alpha u V center radius ha ha' S G H
  have hsmall : 16 * (alpha - 1) ≤ delta := by
    have ht := min_le_right (1 / 32 : ℝ) (delta / 16)
    dsimp only [eps0] at ha'
    linarith
  obtain ⟨r, _, _, T, htF, htB⟩ :=
    suWeakAlphaCoordinate_first_jet_system_coefficients S ha G H
  have hy : suJetBlock (0 : Fin 3) (suFirstJet u center) ∈
      (extChartAt (𝓡 n) b).target := by
    rw [suJetBlock_firstJet_zero]
    exact S.coordinate_range (mem_closedBall_self S.radius_pos.le)
  obtain ⟨O, hO, hcenter, _, hA, hc, hB, hd, nu, hnu, hcoercive, ⟨N⟩⟩ :=
    suAlphaFirstJet_normalization g b ha hsmall (center, suFirstJet u center) hy
  have hJ := hsmooth (3 * n) T (suAlphaFirstJetCoefficients g b alpha)
    htF htB hO hcenter hA hc hB hd hnu hcoercive N
  have hu := (suJetBlock (0 : Fin 3)).contDiff.contDiffAt.comp center hJ
  have he : (suJetBlock (0 : Fin 3)) ∘ suFirstJet u = u :=
    funext (suJetBlock_firstJet_zero u)
  rwa [he] at hu

theorem suWeakAlphaCoordinate_smooth
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 / 32 ∧
      ∀ (b : M) (alpha : ℝ)
        (u : LoopPlane → EuclideanSpace ℝ (Fin n))
        (V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n))
        (center : LoopPlane) (radius : ℝ),
        1 ≤ alpha → alpha ≤ 1 + eps0 →
        SUWeakAlphaCoordinate g b alpha u V center radius → ContDiffAt ℝ ∞ u center := by
  obtain ⟨eh, heh, hehsmall, hholder⟩ := suWeakAlphaCoordinate_holder_of_initial_gain g
  obtain ⟨es, hes, _, hsmooth⟩ := suWeakAlphaCoordinate_smooth_of_holder g
  let eps0 := min eh es
  refine ⟨eps0, lt_min heh hes, (min_le_left _ _).trans hehsmall, ?_⟩
  intro b alpha u V center radius ha ha' S
  have hah : alpha ≤ 1 + eh := ha'.trans (add_le_add le_rfl (min_le_left eh es))
  have has : alpha ≤ 1 + es := ha'.trans (add_le_add le_rfl (min_le_right eh es))
  obtain ⟨G⟩ := suWeakAlphaCoordinate_initial_gain S ha
  obtain ⟨H⟩ := hholder b alpha u V center radius ha hah S G
  exact hsmooth b alpha u V center radius ha has S G H

theorem suWeakAlphaCoordinate_smooth_alpha_one
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) : SUAlphaOneSmoothness g := by
  obtain ⟨eps0, heps, _, hsmooth⟩ := suWeakAlphaCoordinate_smooth g
  intro b u V center radius S
  exact hsmooth b 1 u V center radius le_rfl (by linarith) S

theorem suWeakAlphaSphere_smooth
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ (alpha : ℝ) (S : SUWeakAlphaSphere g eps0 alpha),
      ContMDiff (𝓡 2) (𝓡 n) ∞ S.map := by
  obtain ⟨eps0, heps, _, hsmooth⟩ := suWeakAlphaCoordinate_smooth g
  refine ⟨eps0, heps, ?_⟩
  intro alpha S
  apply suAlphaSphere_smooth_of_coordinates S.map
  intro p
  exact hsmooth (S.map p) alpha (suAlphaChartCoordinate (n := n) S.map p)
    (S.chart p).column ((chartAt LoopPlane p) p) (S.chart p).radius
    S.alpha_mem.1.le S.alpha_mem.2.le (S.chart p).coordinateData

end PoincareConjecture.M60
