import PoincareConjecture.Proofs.M35.Thm12_28.FixedMetricJets
import PoincareConjecture.Proofs.M35.Thm12_28.MetricFamilyWithin
import PoincareConjecture.Proofs.M35.Mathlib.SpatialJetsWithin

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

theorem fixedCylinderMetricCoefficient_eq_pullback {J : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J) (C : GeneralizedSliceCarrier)
    (a Q : ℝ) (f : C.carrier → StandardCapSpace) (q : C.carrier)
    (i j : Fin 3) (p : ℝ × EuclideanSpace ℝ (Fin 3))
    (hp : p.2 ∈ (extChartAt (𝓡 3) q).target)
    (hf : ContMDiffAt (𝓡 3) (𝓡 3) ∞ f ((extChartAt (𝓡 3) q).symm p.2)) :
    fixedCylinderMetricCoefficient F C a Q f q i j p =
      Q * (F.metric (a + p.1 / Q)).pullbackCoefficients
        (f ∘ (extChartAt (𝓡 3) q).symm) p.2
        (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j) := by
  have hc := (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hp)
  have hd := mfderiv_comp p.2 (hf.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp))
  have hv (v : EuclideanSpace ℝ (Fin 3)) :=
    congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) => L v) hd
  exact congrArg (fun r : ℝ => Q * r)
    (congrArg₂ (fun v w : EuclideanSpace ℝ (Fin 3) =>
      (F.metric (a + p.1 / Q)).inner (f ((extChartAt (𝓡 3) q).symm p.2)) v w)
      (hv (EuclideanSpace.basisFun (Fin 3) ℝ i)).symm
      (hv (EuclideanSpace.basisFun (Fin 3) ℝ j)).symm)

theorem fixedCylinderMetricCoefficient_contDiffAt_spatial {J : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J) (C : GeneralizedSliceCarrier)
    (a Q : ℝ) (f : C.carrier → StandardCapSpace) (q : C.carrier)
    (i j : Fin 3) {U : Set C.carrier} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U) (u : ℝ) (p : EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ (extChartAt (𝓡 3) q).target)
    (hpU : (extChartAt (𝓡 3) q).symm p ∈ U) :
    ContDiffAt ℝ ∞ (fun y => fixedCylinderMetricCoefficient F C a Q f q i j (u, y)) p := by
  have hc := (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hp)
  have hparam := (hf.contMDiffAt (hU.mem_nhds hpU)).comp p hc
  have hmetric := (F.metric (a + u / Q)).contDiffAt_pullbackCoefficients hparam
  have hfirst := hmetric.clm_apply (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 3) ℝ i))
  have hs := hfirst.clm_apply (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 3) ℝ j))
  apply ((contDiffAt_const (c := Q)).mul hs).congr_of_eventuallyEq
  have hnear := (continuousAt_extChartAt_symm'' hp).preimage_mem_nhds (hU.mem_nhds hpU)
  filter_upwards [(isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hp, hnear] with y hy hyU
  exact fixedCylinderMetricCoefficient_eq_pullback F C a Q f q i j (u, y) hy
    (hf.contMDiffAt (hU.mem_nhds hyU))

theorem fixedCylinderMetricCoefficient_contDiffOn {J I : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J) (C : GeneralizedSliceCarrier)
    (a Q : ℝ) (f : C.carrier → StandardCapSpace) (q : C.carrier)
    (i j : Fin 3) {U : Set C.carrier} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    {V : Set (EuclideanSpace ℝ (Fin 3))}
    (hV : V ⊆ (extChartAt (𝓡 3) q).target)
    (hVU : MapsTo (extChartAt (𝓡 3) q).symm V U)
    (htime : MapsTo (fun s : ℝ => a + s / Q) I J) :
    ContDiffOn ℝ ∞ (fixedCylinderMetricCoefficient F C a Q f q i j) (I ×ˢ V) := by
  have hfAt (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ V) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ f ((extChartAt (𝓡 3) q).symm z) :=
    hf.contMDiffAt (hU.mem_nhds (hVU hz))
  have hparam (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ V) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ (f ∘ (extChartAt (𝓡 3) q).symm) z :=
    (hfAt z hz).comp z ((contMDiffOn_extChartAt_symm q).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds (hV hz)))
  have hs := metricFamily_contDiffOn_rescaled_pullbackCoefficients F.smooth hparam a Q htime
  have hfirst := hs.clm_apply (contDiffOn_const (c := EuclideanSpace.basisFun (Fin 3) ℝ i))
  have hcoeff := hfirst.clm_apply (contDiffOn_const (c := EuclideanSpace.basisFun (Fin 3) ℝ j))
  apply hcoeff.congr
  intro p hp
  exact fixedCylinderMetricCoefficient_eq_pullback F C a Q f q i j p
    (hV hp.2) (hfAt p.2 hp.2)

theorem fixedCylinderMetricCoefficient_spatialJetAt {J I : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J) (C : GeneralizedSliceCarrier)
    (a Q : ℝ) (f : C.carrier → StandardCapSpace) (q : C.carrier)
    (i j : Fin 3) {U : Set C.carrier} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hI : UniqueDiffOn ℝ I) {u : ℝ} (hu : u ∈ I)
    (htime : MapsTo (fun s : ℝ => a + s / Q) I J)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : p ∈ (extChartAt (𝓡 3) q).target)
    (hpU : (extChartAt (𝓡 3) q).symm p ∈ U) (r : ℕ) :
    iteratedFDeriv ℝ r (fun z => fixedCylinderMetricCoefficient F C a Q f q i j (u, z)) p =
      (iteratedFDerivWithin ℝ r (fixedCylinderMetricCoefficient F C a Q f q i j)
        (I ×ˢ (extChartAt (𝓡 3) q).target) (u, p)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3))) := by
  let V := (extChartAt (𝓡 3) q).target ∩ (extChartAt (𝓡 3) q).symm ⁻¹' U
  have hV : IsOpen V := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
    (isOpen_extChartAt_target q) hU
  have hpV : p ∈ V := ⟨hp, hpU⟩
  have hs := fixedCylinderMetricCoefficient_contDiffOn (I := I) F C a Q f q i j hU hf (V := V)
    (fun _ hz => hz.1) (fun _ hz => hz.2) htime
  have hspatial := iteratedFDeriv_time_slice_of_contDiffOn hI hu hV hs hpV r
  have hset : I ×ˢ V =ᶠ[𝓝 (u, p)] I ×ˢ (extChartAt (𝓡 3) q).target := by
    filter_upwards [continuousAt_snd.preimage_mem_nhds (hV.mem_nhds hpV)] with z hz
    exact propext ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, hz⟩⟩
  have hjet := iteratedFDerivWithin_congr_set (𝕜 := ℝ)
    (f := fixedCylinderMetricCoefficient F C a Q f q i j) hset r
  exact hspatial.trans (congrArg (fun A => A.compContinuousLinearMap
    (fun _ => ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3)))) hjet)

theorem fixedCylinderMetricCoefficient_spatialJet {J I : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J) (C : GeneralizedSliceCarrier)
    (a Q : ℝ) (f : C.carrier → StandardCapSpace) (q : C.carrier)
    (i j : Fin 3) {U : Set C.carrier} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hI : UniqueDiffOn ℝ I) (hzero : (0 : ℝ) ∈ I)
    (htime : MapsTo (fun s : ℝ => a + s / Q) I J)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : p ∈ (extChartAt (𝓡 3) q).target)
    (hpU : (extChartAt (𝓡 3) q).symm p ∈ U) (r : ℕ) :
    iteratedFDeriv ℝ r (fun z => fixedCylinderMetricCoefficient F C a Q f q i j (0, z)) p =
      (iteratedFDerivWithin ℝ r (fixedCylinderMetricCoefficient F C a Q f q i j)
        (I ×ˢ (extChartAt (𝓡 3) q).target) (0, p)).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin 3))) :=
  fixedCylinderMetricCoefficient_spatialJetAt F C a Q f q i j hU hf hI hzero htime hp hpU r

end PoincareConjecture.M35.OrdinaryRealization
