import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Positive.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Pullback

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter PoincareConjecture Manifold IsManifold VectorField
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology Bundle

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X} (hc : RayComparison p)

def positiveConeRadialPotential (a : AsymptoticConePositive p hc) : ℝ :=
  (asymptoticConeRadius hc a.1 : ℝ) ^ 2 / 2

theorem positiveConeRadialPotential_pos (a : AsymptoticConePositive p hc) :
    0 < positiveConeRadialPotential hc a := by
  have ha : 0 < (asymptoticConeRadius hc a.1 : ℝ) := a.property
  dsimp [positiveConeRadialPotential]
  positivity

variable {hc} {n : ℕ}

@[simp] theorem UnitSliceRadialChartData.positiveConeRadialPotential_positiveMap
    (d : UnitSliceRadialChartData hc n) (x : d.source) :
    positiveConeRadialPotential hc (d.positiveMap x) = d.potential x :=
  d.radial x x.property

theorem UnitSliceRadialChartData.sourceMetric_hessian_potential
    (d : UnitSliceRadialChartData hc n) (x : d.source)
    (v w : TangentSpace (𝓡 (n + 1)) x) :
    d.sourceMetric.leviCivitaData.hessian (fun y : d.source => d.potential y) x v w =
      d.sourceMetric.inner x v w := by
  have he := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 (n + 1)) d.source
  have hid (y : d.source) : mfderiv (𝓡 (n + 1)) (𝓡 (n + 1))
      (Subtype.val : d.source → UnitSliceAmbient n) y =
        ContinuousLinearMap.id ℝ (UnitSliceAmbient n) := mfderiv_opens_subtypeVal d.source y
  have hh := d.sourceMetric.leviCivitaData.hessian_comp_of_metric_pullback d.connection
    (he.contMDiff x)
    (Eventually.of_forall (fun y => by
      rw [hid y]
      exact ⟨ContinuousLinearEquiv.refl ℝ (UnitSliceAmbient n), rfl⟩))
    (Eventually.of_forall (fun y a b => by
      simp only [d.sourceMetric_inner, mfderiv_opens_subtypeVal_apply]))
    (d.smooth x) v w
  simpa only [Function.comp_def, mfderiv_opens_subtypeVal_apply,
    d.hessian x x.property, d.sourceMetric_inner] using hh

theorem UnitSliceRadialChartData.sourceMetric_levelQ_potential
    (d : UnitSliceRadialChartData hc n) (x : d.source) :
    d.sourceMetric.leviCivitaData.levelQ (fun y : d.source => d.potential y) x =
      2 * d.potential x := by
  have he := Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 (n + 1)) d.source
  have hid : mfderiv (𝓡 (n + 1)) (𝓡 (n + 1))
      (Subtype.val : d.source → UnitSliceAmbient n) x =
        ContinuousLinearMap.id ℝ (UnitSliceAmbient n) := mfderiv_opens_subtypeVal d.source x
  have hinv : (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1))
      (Subtype.val : d.source → UnitSliceAmbient n) x).IsInvertible := by
    rw [hid]
    exact ⟨ContinuousLinearEquiv.refl ℝ (UnitSliceAmbient n), rfl⟩
  have hg := d.sourceMetric.leviCivitaData.gradient_comp_eq_mpullback d.connection
    (he.mdifferentiable (by simp) x) (d.smooth.mdifferentiable (by simp) x) hinv
    (fun a b => by simp only [d.sourceMetric_inner, mfderiv_opens_subtypeVal_apply])
  have hgrad : d.sourceMetric.leviCivitaData.gradient (fun y : d.source => d.potential y) x =
      d.connection.gradient d.potential x := by
    have hpush := congrArg (fun v => mfderiv (𝓡 (n + 1)) (𝓡 (n + 1))
      (Subtype.val : d.source → UnitSliceAmbient n) x v) hg
    simpa only [Function.comp_def, mpullback, hinv.self_apply_inverse,
      mfderiv_opens_subtypeVal_apply] using hpush
  simpa only [LeviCivitaData.levelQ, hgrad, d.sourceMetric_inner] using d.eikonal x x.property

variable (hne : Nonempty (AsymptoticConePositive p hc))
  (hcover : ∀ z : AsymptoticConeUnitSlice p hc,
    ∃ (d : UnitSliceRadialChartData hc n) (x : d.Level), (d.levelHomeomorph x).1 = z)

theorem contMDiff_positiveConeRadialPotential :
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ (positiveConeRadialPotential hc) := by
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro a
  obtain ⟨d, ha⟩ := positiveCone_radialAtlas_covers hc n hne hcover a
  have hmax : d.positiveChart hne ∈ maximalAtlas (𝓡 (n + 1)) ∞
      (AsymptoticConePositive p hc) := subset_maximalAtlas ⟨d, rfl⟩
  have hs := (d.smooth (d.positiveChart hne a)).comp a
    (contMDiffAt_of_mem_maximalAtlas hmax ha)
  apply hs.congr_of_eventuallyEq
  filter_upwards [(d.positiveChart hne).open_source.mem_nhds ha] with b hb
  change (asymptoticConeRadius hc b.1 : ℝ) ^ 2 / 2 =
    d.potential (d.ambientChart.symm b.1)
  have hb' : b.1 ∈ d.ambientChart.target := by
    simpa only [d.positiveChart_source, mem_ofPred_eq] using hb
  have hr := d.radial _ (d.ambientChart.map_target hb')
  rwa [d.ambientChart.right_inv hb'] at hr

include hcover in
private theorem exists_positiveMap_preimage (a : AsymptoticConePositive p hc) :
    ∃ (d : UnitSliceRadialChartData hc n) (x : d.source), d.positiveMap x = a := by
  obtain ⟨d, x, hx, hvalue, _⟩ := exists_dilated_radial_model_at_positive_point hc hcover a
  exact ⟨d.dilate (asymptoticConeRadius hc a.1) a.property, ⟨x, hx⟩, Subtype.ext hvalue⟩

theorem positiveConeRadialPotential_hessian :
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ (a : AsymptoticConePositive p hc) (v w : TangentSpace (𝓡 (n + 1)) a),
      (positiveConeMetric hne hcover).leviCivitaData.hessian
        (positiveConeRadialPotential hc) a v w = (positiveConeMetric hne hcover).inner a v w := by
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro a
  obtain ⟨d, x, rfl⟩ := exists_positiveMap_preimage hcover a
  intro v w
  have he := d.isLocalDiffeomorph_positiveMap hne hcover
  have hinv (y : d.source) :
      (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.positiveMap y).IsInvertible :=
    ⟨(he y).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have hmetric (y : d.source) (b c : TangentSpace (𝓡 (n + 1)) y) :
      d.sourceMetric.inner y b c = (positiveConeMetric hne hcover).inner (d.positiveMap y)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.positiveMap y b)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.positiveMap y c) := by
    rw [d.sourceMetric_inner]
    exact positiveConeMetric_inner hne hcover d y b c
  have hcomp : positiveConeRadialPotential hc ∘ d.positiveMap =
      (fun y : d.source => d.potential y) := funext (fun y => d.positiveConeRadialPotential_positiveMap y)
  have hh := d.sourceMetric.leviCivitaData.hessian_comp_of_metric_pullback
    (positiveConeMetric hne hcover).leviCivitaData (he.contMDiff x)
    (Eventually.of_forall hinv) (Eventually.of_forall hmetric)
    (contMDiff_positiveConeRadialPotential hne hcover (d.positiveMap x))
    ((mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.positiveMap x).inverse v)
    ((mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.positiveMap x).inverse w)
  rw [hcomp, d.sourceMetric_hessian_potential, hmetric] at hh
  simpa only [(hinv x).self_apply_inverse] using hh.symm

theorem positiveConeRadialPotential_levelQ :
    letI := positiveConeChartedSpace hc n hne hcover
    letI := positiveCone_isManifold hc n hne hcover
    ∀ a : AsymptoticConePositive p hc,
      (positiveConeMetric hne hcover).leviCivitaData.levelQ (positiveConeRadialPotential hc) a =
        2 * positiveConeRadialPotential hc a := by
  let := positiveConeChartedSpace hc n hne hcover
  let := positiveCone_isManifold hc n hne hcover
  intro a
  obtain ⟨d, x, rfl⟩ := exists_positiveMap_preimage hcover a
  have he := d.isLocalDiffeomorph_positiveMap hne hcover
  have hinv : (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.positiveMap x).IsInvertible :=
    ⟨(he x).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have hmetric (b c : TangentSpace (𝓡 (n + 1)) x) :
      d.sourceMetric.inner x b c = (positiveConeMetric hne hcover).inner (d.positiveMap x)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.positiveMap x b)
        (mfderiv (𝓡 (n + 1)) (𝓡 (n + 1)) d.positiveMap x c) := by
    rw [d.sourceMetric_inner]
    exact positiveConeMetric_inner hne hcover d x b c
  have hcomp : positiveConeRadialPotential hc ∘ d.positiveMap =
      (fun y : d.source => d.potential y) := funext (fun y => d.positiveConeRadialPotential_positiveMap y)
  have hg := d.sourceMetric.leviCivitaData.gradient_comp_eq_mpullback
    (positiveConeMetric hne hcover).leviCivitaData (he.mdifferentiable (by simp) x)
    ((contMDiff_positiveConeRadialPotential hne hcover).mdifferentiable (by simp) (d.positiveMap x))
    hinv hmetric
  have hq := d.sourceMetric_levelQ_potential x
  rw [← hcomp] at hq
  simp only [LeviCivitaData.levelQ, hg, hmetric, mpullback, hinv.self_apply_inverse] at hq
  rw [d.positiveConeRadialPotential_positiveMap]
  exact hq

end Poincare.AncientVolume.ScalarRatio
