import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Positive.RadialPotential
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Positive.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.QuotientCoefficients










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

open Set Filter PoincareConjecture Poincare.Gluing Manifold IsManifold VectorField
open scoped Manifold ContDiff Topology Bundle

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} (hc : RayComparison p) {n : ℕ}
  (hne : Nonempty (AsymptoticConePositive p hc))
  (hcover : ∀ z : AsymptoticConeUnitSlice p hc,
    ∃ (d : UnitSliceRadialChartData hc n) (x : d.Level), (d.levelHomeomorph x).1 = z)
  {ι : Type*} (U : ι → Set (EuclideanSpace ℝ (Fin (n + 1))))
  (hU : ∀ i, IsOpen (U i)) [∀ i, Nonempty (Piece U i)]
  (O : OverlapSystem (fun i => Piece U i))
  (g : ι → RiemannianMetric (n + 1) (EuclideanSpace ℝ (Fin (n + 1))))
  (f : Quotient O.setoid → AsymptoticConePositive p hc)
  (hf : Topology.IsOpenEmbedding f)
  (hdist : ∀ i (x y : Piece U i), dist (f (O.include i x)) (f (O.include i y)) =
    ((g i).edist x y).toReal)


def positiveConeRealizationMetric :
    letI := quotientChartedSpace U hU O
    letI := RiemannianMetric.quotient_isManifold_of_isometric_realization U hU O g f hdist
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    RiemannianMetric (n + 1) (Quotient O.setoid) := by
  let := quotientChartedSpace U hU O
  let := RiemannianMetric.quotient_isManifold_of_isometric_realization U hU O g f hdist
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  exact (positiveConeMetric hne hcover).pullbackOfLocalDiffeomorph f
    (isLocalDiffeomorph_positiveCone_realization hc hne hcover U hU O g f hf hdist).2

theorem positiveConeRealizationMetric_inner :
    letI := quotientChartedSpace U hU O
    letI := RiemannianMetric.quotient_isManifold_of_isometric_realization U hU O g f hdist
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ (x : Quotient O.setoid) (v w : TangentSpace (𝓡 (n + 1)) x),
      (positiveConeRealizationMetric hc hne hcover U hU O g f hf hdist).inner x v w =
        (positiveConeMetric hne hcover).inner (f x)
          (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) f x v)
          (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) f x w) := by
  let := quotientChartedSpace U hU O
  let := RiemannianMetric.quotient_isManifold_of_isometric_realization U hU O g f hdist
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro x v w
  rfl



theorem positiveConeRealizationMetric_pullbackCoefficients :
    letI := quotientChartedSpace U hU O
    letI := RiemannianMetric.quotient_isManifold_of_isometric_realization U hU O g f hdist
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ i, EqOn
      ((positiveConeRealizationMetric hc hne hcover U hU O g f hf hdist).pullbackCoefficients
        (ChartDistance.chartParametrization U hU (O.include i)))
      (g i).euclideanCoefficients (U i) := by
  let := quotientChartedSpace U hU O
  let := RiemannianMetric.quotient_isManifold_of_isometric_realization U hU O g f hdist
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  have hfd := (isLocalDiffeomorph_positiveCone_realization hc hne hcover U hU O g f hf hdist).2
  intro i x hx
  let ci := quotientChart U hU O i
  have hxci : x ∈ ci.target := by rw [quotientChart_target]; exact hx
  let : Nonempty (Quotient O.setoid) := ⟨ci.symm x⟩
  let fOpen := hf.toOpenPartialHomeomorph
  obtain ⟨d, hxd⟩ := positiveCone_radialAtlas_covers hc n hne hcover (f (ci.symm x))
  let cd := d.positiveChart hne
  let A := ci.symm.trans fOpen
  let T := A.trans cd
  have hA : ∀ a ∈ A.source, ∀ b ∈ A.source,
      dist (A a) (A b) = ((g i).edist a b).toReal := by
    intro a ha b hb
    have haU : a ∈ U i := quotientChart_target U hU O i ▸ ha.1
    have hbU : b ∈ U i := quotientChart_target U hU O i ▸ hb.1
    change dist (f ((quotientChart U hU O i).symm a))
      (f ((quotientChart U hU O i).symm b)) = _
    rw [quotientChart_symm_apply U hU O i haU, quotientChart_symm_apply U hU O i hbU]
    exact hdist i ⟨a, haU⟩ ⟨b, hbU⟩
  have hT := (g i).smooth_isometric_charts_of_edist_eq d.metric T
    ((g i).edist_eq_on_isometric_chart_transition d.metric A cd.symm hA
      (fun a ha b hb => d.positiveChart_symm_distance hne ha hb))
  have hxT : x ∈ T.source := ⟨⟨hxci, mem_univ _⟩, hxd⟩
  have hciAtlas : ci ∈ maximalAtlas (𝓡 (n + 1)) ∞ (Quotient O.setoid) :=
    subset_maximalAtlas ⟨i, rfl⟩
  have hcdAtlas : cd ∈ maximalAtlas (𝓡 (n + 1)) ∞ (AsymptoticConePositive p hc) :=
    subset_maximalAtlas ⟨d, rfl⟩
  have hciDiff : MDifferentiableAt (𝓡 (n + 1)) (𝓡 (n + 1)) ci.symm x :=
    ((contMDiffOn_symm_of_mem_maximalAtlas hciAtlas).contMDiffAt
      (ci.open_target.mem_nhds hxci)).mdifferentiableAt (by simp)
  have hcdDiff : MDifferentiableAt (𝓡 (n + 1)) (𝓡 (n + 1)) cd.symm (T x) :=
    ((contMDiffOn_symm_of_mem_maximalAtlas hcdAtlas).contMDiffAt
      (cd.open_target.mem_nhds (cd.map_source hxT.2))).mdifferentiableAt (by simp)
  have hTDiff := (hT.1.contMDiffAt (T.open_source.mem_nhds hxT)).mdifferentiableAt (by simp)
  have hcomp : f ∘ ci.symm =ᶠ[𝓝 x] cd.symm ∘ T := by
    filter_upwards [T.open_source.mem_nhds hxT] with y hy
    exact (cd.left_inv hy.2).symm
  have hleft := mfderiv_comp x (hfd.mdifferentiable (by simp) (ci.symm x)) hciDiff
  have hright := mfderiv_comp x hcdDiff hTDiff
  have hderiv (v : EuclideanSpace ℝ (Fin (n + 1))) :
      mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) f (ci.symm x)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) ci.symm x v) =
      mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) cd.symm (T x)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) T x v) := by
    have hd := congrArg (fun L => L v)
      (hcomp.mfderiv_eq (I := 𝓡 (n + 1)) (I' := 𝓡 (n + 1)))
    erw [hleft, hright] at hd
    exact hd
  have hbase : cd.symm (T x) = f (ci.symm x) := cd.left_inv hxT.2
  have hparam : ChartDistance.chartParametrization U hU (O.include i) = ci.symm := rfl
  rw [hparam]
  ext v w
  change (positiveConeMetric hne hcover).inner (f (ci.symm x))
    (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) f (ci.symm x)
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) ci.symm x v))
    (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) f (ci.symm x)
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) ci.symm x w)) = (g i).inner x v w
  rw [hderiv v, hderiv w]
  have hm := d.positiveChart_symm_inner hne hcover (T x) (cd.map_source hxT.2)
    (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) T x v)
    (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) T x w)
  rw [hbase] at hm
  exact hm.symm.trans (hT.2.2 x hxT v w)



theorem positiveConeRealizationMetric_radialPotential :
    letI := quotientChartedSpace U hU O
    letI := RiemannianMetric.quotient_isManifold_of_isometric_realization U hU O g f hdist
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    let gQ := positiveConeRealizationMetric hc hne hcover U hU O g f hf hdist
    let u := positiveConeRadialPotential hc ∘ f
    ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ u ∧
      (∀ x v w, gQ.leviCivitaData.hessian u x v w = gQ.inner x v w) ∧
      ∀ x, gQ.leviCivitaData.levelQ u x = 2 * u x := by
  let := quotientChartedSpace U hU O
  let := RiemannianMetric.quotient_isManifold_of_isometric_realization U hU O g f hdist
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  let gQ := positiveConeRealizationMetric hc hne hcover U hU O g f hf hdist
  have hfd := (isLocalDiffeomorph_positiveCone_realization hc hne hcover U hU O g f hf hdist).2
  have hinv (x : Quotient O.setoid) :
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) f x).IsInvertible :=
    ⟨(hfd x).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have hmetric := positiveConeRealizationMetric_inner hc hne hcover U hU O g f hf hdist
  have hpotential := contMDiff_positiveConeRadialPotential hne hcover
  refine ⟨hpotential.comp hfd.contMDiff, ?_, ?_⟩
  · intro x v w
    have hh := gQ.leviCivitaData.hessian_comp_of_metric_pullback
      (positiveConeMetric hne hcover).leviCivitaData (hfd.contMDiff x)
      (Eventually.of_forall hinv) (Eventually.of_forall hmetric) (hpotential (f x)) v w
    rw [positiveConeRadialPotential_hessian hne hcover] at hh
    exact hh.trans (hmetric x v w).symm
  · intro x
    have hg := gQ.leviCivitaData.gradient_comp_eq_mpullback
      (positiveConeMetric hne hcover).leviCivitaData
      (hfd.mdifferentiable (by simp) x) (hpotential.mdifferentiable (by simp) (f x))
      (hinv x) (hmetric x)
    change gQ.inner x (gQ.leviCivitaData.gradient (positiveConeRadialPotential hc ∘ f) x)
      (gQ.leviCivitaData.gradient (positiveConeRadialPotential hc ∘ f) x) = _
    rw [hg, hmetric]
    simp only [mpullback, (hinv x).self_apply_inverse]
    exact positiveConeRadialPotential_levelQ hne hcover (f x)

end Poincare.AncientVolume.ScalarRatio
