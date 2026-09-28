import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.GlobalPairing
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Regularity
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.TestOperator

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Parabolic.WeakRegularity

namespace PoincareConjecture.RicciFlow.ConjugateHeat

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def spacetimeChartPushforward
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (ψ : Spacetime n → ℝ) : M × ℝ → ℝ :=
  (e.target ×ˢ univ).indicator (fun z => ψ (e.symm z.1, z.2))

theorem spacetimeChartPushforward_apply
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (ψ : Spacetime n → ℝ) {z : M × ℝ} (hz : z.1 ∈ e.target) :
    spacetimeChartPushforward e ψ z = ψ (e.symm z.1, z.2) :=
  indicator_of_mem (show z ∈ e.target ×ˢ univ from ⟨hz, mem_univ _⟩) _

private theorem compact_forward_spacetime_support
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {ψ : Spacetime n → ℝ} (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ e.source ×ˢ univ) :
    IsCompact ((fun z : Spacetime n => (e z.1, z.2)) '' tsupport ψ) := by
  apply hc.isCompact.image_of_continuousOn
  have hforward : ContinuousOn (fun z : Spacetime n => (e z.1, z.2))
      (e.source ×ˢ univ) :=
    (e.continuousOn.comp continuous_fst.continuousOn
      (fun z hz => hz.1)).prodMk continuous_snd.continuousOn
  exact hforward.mono hs

theorem tsupport_spacetimeChartPushforward_subset_image
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {ψ : Spacetime n → ℝ} (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ e.source ×ˢ univ) :
    tsupport (spacetimeChartPushforward e ψ) ⊆
      (fun z : Spacetime n => (e z.1, z.2)) '' tsupport ψ := by
  apply closure_minimal _ (compact_forward_spacetime_support e hc hs).isClosed
  intro z hz
  have htarget : z.1 ∈ e.target := by
    by_contra h
    exact hz (indicator_of_notMem (fun hz' => h hz'.1) _)
  refine ⟨(e.symm z.1, z.2), subset_tsupport ψ ?_, ?_⟩
  · simpa only [Function.mem_support, spacetimeChartPushforward_apply e ψ htarget] using hz
  · simp only [e.right_inv htarget, Prod.eta]

theorem tsupport_spacetimeChartPushforward_subset
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {ψ : Spacetime n → ℝ} {T : Set ℝ} (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ e.source ×ˢ T) :
    tsupport (spacetimeChartPushforward e ψ) ⊆ e.target ×ˢ T := by
  have hs' := hs.trans (prod_mono Subset.rfl (subset_univ T))
  intro z hz
  obtain ⟨y, hy, rfl⟩ := tsupport_spacetimeChartPushforward_subset_image e hc hs' hz
  exact ⟨e.map_source (hs hy).1, (hs hy).2⟩

theorem hasCompactSupport_spacetimeChartPushforward
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {ψ : Spacetime n → ℝ} (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ e.source ×ˢ univ) :
    HasCompactSupport (spacetimeChartPushforward e ψ) :=
  (compact_forward_spacetime_support e hc hs).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_spacetimeChartPushforward_subset_image e hc hs)

theorem contMDiff_spacetimeChartPushforward
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {ψ : Spacetime n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ e.source ×ˢ univ) :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (spacetimeChartPushforward e ψ) := by
  intro z
  by_cases hz : z.1 ∈ e.target
  · have hmap : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Spacetime n) ∞
        (fun y : M × ℝ => (e.symm y.1, y.2)) z :=
      ((hei.contMDiffAt (e.open_target.mem_nhds hz)).comp z
        contMDiffAt_fst).prodMk_space contMDiffAt_snd
    apply (hψ.contMDiff.contMDiffAt.comp z hmap).congr_of_eventuallyEq
    filter_upwards [(continuous_fst.tendsto z) (e.open_target.mem_nhds hz)] with y hy
    exact spacetimeChartPushforward_apply e ψ hy
  · apply contMDiffAt_const.congr_of_eventuallyEq
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hz'
    exact hz (tsupport_spacetimeChartPushforward_subset e hc hs hz').1

theorem spacetimeChartPullback_pushforward
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    {ψ : Spacetime n → ℝ} (hs : tsupport ψ ⊆ e.source ×ˢ univ) :
    spacetimeChartPullback e (spacetimeChartPushforward e ψ) = ψ := by
  funext z
  by_cases hz : z.1 ∈ e.source
  · rw [spacetimeChartPullback_apply e _ hz,
      spacetimeChartPushforward_apply e ψ (e.map_source hz), e.left_inv hz]
  · rw [show ψ z = 0 from image_eq_zero_of_notMem_tsupport (fun h => hz (hs h).1)]
    exact indicator_of_notMem (fun h => hz h.1) _

theorem integrableOn_coordinate_heat_pairing
    (F : RicciFlow n M (Iio (0 : ℝ)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {u : Spacetime n → ℝ} (hu : ContinuousOn u (e.source ×ˢ Ioi (0 : ℝ)))
    {ψ : Spacetime n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ e.source ×ˢ Ioi (0 : ℝ)) :
    IntegrableOn (fun z : Spacetime n => BackwardCoordinates.density F e z * u z *
      (-Canonical.timeDeriv ψ z - (F.connection (-z.2)).laplacian
        (fun y => ψ (e.symm y, z.2)) (e z.1))) (e.source ×ˢ Ioi (0 : ℝ)) := by
  let D := e.source ×ˢ Ioi (0 : ℝ)
  let a := BackwardCoordinates.principal F e
  let b := BackwardCoordinates.drift F e
  let A := fun z => BackwardCoordinates.density F e z * u z *
    Canonical.diffusionTest a b ψ z
  have hden : ContDiffOn ℝ ∞ (BackwardCoordinates.density F e) D := by
    simpa only [BackwardCoordinates.domain_Iio_zero] using
      BackwardCoordinates.contDiffOn_density F e he hei
  have ha (i j) : ContDiffOn ℝ ∞ (a i j) D := by
    simpa only [BackwardCoordinates.domain_Iio_zero] using
      BackwardCoordinates.contDiffOn_principal F e he hei i j
  have hb (i) : ContDiffOn ℝ ∞ (b i) D := by
    simpa only [BackwardCoordinates.domain_Iio_zero] using
      BackwardCoordinates.contDiffOn_drift F e he hei i
  have hd (i) : ContDiff ℝ ∞ (Canonical.spatialDeriv i ψ) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hdd (i j) : ContDiff ℝ ∞ (Canonical.spatialDeriv j (Canonical.spatialDeriv i ψ)) :=
    ((hd i).fderiv_right (by simp)).clm_apply contDiff_const
  have ht : ContDiff ℝ ∞ (Canonical.timeDeriv ψ) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hop : ContDiffOn ℝ ∞ (Canonical.diffusionTest a b ψ) D :=
    (ht.contDiffOn.neg.sub (ContDiffOn.sum (fun i _ => ContDiffOn.sum
      (fun j _ => (ha i j).mul (hdd i j).contDiffOn)))).sub
      (ContDiffOn.sum (fun i _ => (hb i).mul (hd i).contDiffOn))
  have hAc : ContinuousOn A D := (hden.continuousOn.mul hu).mul hop.continuousOn
  have hsA : Function.support A ⊆ tsupport ψ := by
    intro z hz
    by_contra hzψ
    exact hz (by
      dsimp only [A]
      rw [Canonical.diffusionTest_eq_zero_of_notMem_tsupport a b ψ hzψ, mul_zero])
  have hAi : Integrable A := (integrableOn_iff_integrable_of_support_subset hsA).mp
    ((hAc.mono hs).integrableOn_compact hc.isCompact)
  apply hAi.integrableOn.congr_fun _ (e.open_source.prod isOpen_Ioi).measurableSet
  intro z hz
  have hz' : z ∈ BackwardCoordinates.domain (Iio (0 : ℝ)) e := by
    simpa only [BackwardCoordinates.domain_Iio_zero] using hz
  dsimp only [A]
  rw [BackwardCoordinates.laplacian_coordinateTest_forward F e he hei hψ hz']
  dsimp only [Canonical.diffusionTest, a, b]
  ring

theorem coordinate_pairing_eq_zero_of_weakPairing_eq_zero
    (F : RicciFlow n M (Iio (0 : ℝ)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {u : M × ℝ → ℝ} (hu : ContinuousOn u (univ ×ˢ Ioi (0 : ℝ)))
    (hweak : ∀ φ : M × ℝ → ℝ,
      ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ univ ×ˢ Ioi (0 : ℝ) → weakPairing F u φ = 0)
    {ψ : Spacetime n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ e.source ×ˢ Ioi (0 : ℝ)) :
    (∫ z in e.source ×ˢ Ioi (0 : ℝ),
      BackwardCoordinates.density F e z * u (e z.1, z.2) *
        (-Canonical.timeDeriv ψ z - (F.connection (-z.2)).laplacian
          (fun y => ψ (e.symm y, z.2)) (e z.1))) = 0 := by
  have hs' := hs.trans (prod_mono Subset.rfl (subset_univ (Ioi (0 : ℝ))))
  let φ := spacetimeChartPushforward e ψ
  have hφ := contMDiff_spacetimeChartPushforward e hei hψ hc hs'
  have hφc := hasCompactSupport_spacetimeChartPushforward e hc hs'
  have hφs := tsupport_spacetimeChartPushforward_subset e hc hs
  have hpull : spacetimeChartPullback e φ = ψ := spacetimeChartPullback_pushforward e hs'
  have huc : ContinuousOn (fun z : Spacetime n => u (e z.1, z.2))
      (e.source ×ˢ Ioi (0 : ℝ)) :=
    hu.comp ((e.continuousOn.comp continuous_fst.continuousOn
      (fun z hz => hz.1)).prodMk continuous_snd.continuousOn)
      (fun z hz => ⟨mem_univ _, hz.2⟩)
  have hBi := integrableOn_coordinate_heat_pairing F e he hei huc hψ hc hs
  have hBi' : IntegrableOn (fun z : Spacetime n =>
      (F.metric (-z.2)).pullbackVolumeDensity e z.1 * u (e z.1, z.2) *
        (-Canonical.timeDeriv (spacetimeChartPullback e φ) z -
          (F.connection (-z.2)).laplacian
            (fun y => spacetimeChartPullback e φ (e.symm y, z.2)) (e z.1)))
      (e.source ×ˢ Ioi (0 : ℝ)) := by
    rw [hpull]
    exact hBi
  have hbridge := weakPairing_eq_neg_coordinate_pairing F e he hei hu hφ hφc hφs hBi'
  rw [hweak φ hφ hφc (hφs.trans (prod_mono (subset_univ _) Subset.rfl)), hpull] at hbridge
  exact neg_eq_zero.mp hbridge.symm

theorem potential_contMDiffOn_of_weakPairing_eq_zero
    (F : RicciFlow n M (Iio (0 : ℝ))) {l : M × ℝ → ℝ}
    (hl : ContinuousOn l (univ ×ˢ Ioi (0 : ℝ)))
    (hweak : ∀ φ : M × ℝ → ℝ,
      ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ univ ×ˢ Ioi (0 : ℝ) →
      weakPairing F (fun z => z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l z)) φ = 0) :
    ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ l (univ ×ˢ Ioi (0 : ℝ)) := by
  let u : M × ℝ → ℝ := fun z => z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l z)
  have hu : ContinuousOn u (univ ×ˢ Ioi (0 : ℝ)) :=
    (continuousOn_snd.rpow_const (fun z hz => Or.inl (ne_of_gt hz.2))).mul
      (Real.continuous_exp.comp_continuousOn hl.neg)
  intro z hz
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) z.1).symm
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart_symm
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart
  let D := e.source ×ˢ Ioi (0 : ℝ)
  have hD : IsOpen D := e.open_source.prod isOpen_Ioi
  have hDdomain : D ⊆ BackwardCoordinates.domain (Iio (0 : ℝ)) e := by
    rw [BackwardCoordinates.domain_Iio_zero]
  have hlc : ContinuousOn (fun y : Spacetime n => l (e y.1, y.2)) D :=
    hl.comp ((e.continuousOn.comp continuous_fst.continuousOn
      (fun y hy => hy.1)).prodMk continuous_snd.continuousOn)
      (fun y hy => ⟨mem_univ _, hy.2⟩)
  have hc : ContDiffOn ℝ ∞ (fun y : Spacetime n => l (e y.1, y.2)) D := by
    apply BackwardCoordinates.potential_contDiffOn_of_weak_heat_pairing F e he hei
      hD hDdomain (fun y hy => hy.2) hlc
    intro ψ hψ hψc hψD
    have hp := coordinate_pairing_eq_zero_of_weakPairing_eq_zero F e he hei hu hweak hψ hψc hψD
    simpa only [u, mul_assoc] using hp
  have hp : z.1 ∈ e.target := mem_chart_source _ z.1
  have hx : (e.symm z.1, z.2) ∈ D := ⟨e.map_target hp, hz.2⟩
  have hmap : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Spacetime n) ∞
      (fun y : M × ℝ => (e.symm y.1, y.2)) z :=
    ((hei.contMDiffAt (e.open_target.mem_nhds hp)).comp z
      contMDiffAt_fst).prodMk_space contMDiffAt_snd
  apply (((hc.contDiffAt (hD.mem_nhds hx)).contMDiffAt.comp z hmap).congr_of_eventuallyEq
    ?_).contMDiffWithinAt
  filter_upwards [(continuous_fst.tendsto z) (e.open_target.mem_nhds hp)] with y hy
  change l y = l (e (e.symm y.1), y.2)
  rw [e.right_inv hy]

end PoincareConjecture.RicciFlow.ConjugateHeat
