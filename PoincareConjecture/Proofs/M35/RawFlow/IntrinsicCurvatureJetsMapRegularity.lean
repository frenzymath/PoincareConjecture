import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsCoordinateFamily
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsMapTension
import PoincareConjecture.Proofs.M35.RadialGauge.ComposedMapJets
import PoincareConjecture.Proofs.M35.RadialGauge.TensionFamily
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawJointInverse
import PoincareConjecture.Proofs.M03.ConnectionExistence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open RadialGauge Heat

private theorem composed_smooth_spatial_jets
    {F S : ℝ → StandardCapSpace → StandardCapSpace} {J : Set ℝ}
    (hFs : ∀ t ∈ J, ContDiff ℝ ∞ (F t))
    (hSs : ∀ t ∈ J, ContDiff ℝ ∞ (S t))
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (J ×ˢ univ))
    (hF : ContDiffOn ℝ 1 (Function.uncurry F) (J ×ˢ univ))
    (hDF : ContDiffOn ℝ 1
      (fun p : ℝ × StandardCapSpace => fderiv ℝ (F p.1) p.2) (J ×ˢ univ))
    (hDDF : ContDiffOn ℝ 1
      (fun p : ℝ × StandardCapSpace => fderiv ℝ (fderiv ℝ (F p.1)) p.2) (J ×ˢ univ)) :
    ContDiffOn ℝ 1 (fun p : ℝ × StandardCapSpace => F p.1 (S p.1 p.2)) (J ×ˢ univ) ∧
    ContDiffOn ℝ 1
      (fun p : ℝ × StandardCapSpace => fderiv ℝ (F p.1 ∘ S p.1) p.2) (J ×ˢ univ) ∧
    ContDiffOn ℝ 1
      (fun p : ℝ × StandardCapSpace => fderiv ℝ (fderiv ℝ (F p.1 ∘ S p.1)) p.2)
      (J ×ˢ univ) := by
  have hDS := raw_family_spatial_fderiv_contDiffOn (f := S) hS
  have hDDS := raw_family_spatial_fderiv_contDiffOn
    (f := fun t x => fderiv ℝ (S t) x) hDS
  refine ⟨?_, composed_map_fderiv_joint_c1 hFs hSs (hS.of_le (by simp)) hDF
    (hDS.of_le (by simp)), composed_map_hessian_joint_c1 hFs hSs (hS.of_le (by simp)) hDF
      (hDS.of_le (by simp)) hDDF (hDDS.of_le (by simp))⟩
  exact hF.comp (contDiffOn_fst.prodMk (hS.of_le (by simp)))
    (fun _ hp => ⟨hp.1, mem_univ _⟩)

theorem rawIntrinsicGaugeMap_joint_c2
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀)
    (hrotation : ∀ t ∈ Ico 0 G.lifetime,
      ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
        (G.flow.metric t).inner (standardRotation A x)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
          (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
    {T t₀ delta : ℝ} (hTlt : T < G.lifetime) (ht₀ : t₀ ∈ Ico 0 T)
    (hdT : delta ≤ T - t₀) {w : ℝ → ℝ → ℝ}
    (hws : ∀ t ∈ Icc 0 delta, ContDiff ℝ ∞ (w t) ∧ Function.Even (w t))
    (hw : ContDiffOn ℝ 1 (Function.uncurry w) (Ioo 0 delta ×ˢ univ))
    (hF : ContDiffOn ℝ 1
      (fun p : ℝ × StandardCapSpace => euclideanGauge (fun x => w p.1 ‖x‖) p.2)
      (Ioo 0 delta ×ˢ univ))
    (hDF : ContDiffOn ℝ 1
      (fun p : ℝ × StandardCapSpace => fderiv ℝ (euclideanGauge (fun x => w p.1 ‖x‖)) p.2)
      (Ioo 0 delta ×ˢ univ))
    (hDDF : ContDiffOn ℝ 1
      (fun p : ℝ × StandardCapSpace =>
        fderiv ℝ (fderiv ℝ (euclideanGauge (fun x => w p.1 ‖x‖))) p.2)
      (Ioo 0 delta ×ˢ univ))
    (hPDE : ∀ t ∈ Ioo 0 delta, ∀ r > 0, HasDerivAt (fun a => mapRadius (w a) r)
      (harmonicRadialOperator 3 (rawWarpingRadius P G hrotation (t₀ + t))
        (rawWarpingRadius P G hrotation t₀) (rawRadialVelocity P G hrotation (t₀ + t))
        (mapRadius (w t)) r) t) :
    ContDiffOn ℝ 2
      (fun p : ℝ × StandardCapSpace => rawIntrinsicGaugeMap G t₀ w p.1 p.2)
      (Ioo 0 delta ×ˢ univ) := by
  have hshift (t : ℝ) (ht : t ∈ Ioo 0 delta) : t₀ + t ∈ Ioo 0 G.lifetime := by
    refine ⟨add_pos_of_nonneg_of_pos ht₀.1 ht.1, lt_of_le_of_lt ?_ hTlt⟩
    linarith only [ht.2, hdT]
  have hsmap : MapsTo (fun p : ℝ × StandardCapSpace => (t₀ + p.1, p.2))
      (Ioo 0 delta ×ˢ univ) (Ioo 0 G.lifetime ×ˢ univ) :=
    fun p hp => ⟨hshift p.1 hp.1, mem_univ _⟩
  have hsmap' : MapsTo (fun p : ℝ × StandardCapSpace => (t₀ + p.1, p.2))
      (Ioo 0 delta ×ˢ univ) (Ico 0 G.lifetime ×ˢ univ) :=
    fun p hp => ⟨⟨(hshift p.1 hp.1).1.le, (hshift p.1 hp.1).2⟩, mem_univ _⟩
  let S (t : ℝ) (x : StandardCapSpace) := intrinsicSpatialCoordinate (G.flow.metric (t₀ + t)) x
  let F (t : ℝ) := euclideanGauge (fun x : StandardCapSpace => w t ‖x‖)
  have hshiftMap : ContDiffOn ℝ ∞
      (fun p : ℝ × StandardCapSpace => (t₀ + p.1, p.2)) (Ioo 0 delta ×ˢ univ) :=
    (contDiffOn_const.add contDiffOn_fst).prodMk contDiffOn_snd
  have hS : ContDiffOn ℝ ∞ (Function.uncurry S) (Ioo 0 delta ×ˢ univ) := by
    have hcomp := (raw_intrinsicSpatialCoordinate_contDiffOn G hrotation).comp
      (f := fun p : ℝ × StandardCapSpace => (t₀ + p.1, p.2)) hshiftMap hsmap
    exact hcomp
  have hSs (t : ℝ) (ht : t ∈ Ioo 0 delta) : ContDiff ℝ ∞ (S t) :=
    intrinsicSpatialCoordinate_contDiff (G.flow.metric (t₀ + t))
      (hrotation (t₀ + t) ⟨(hshift t ht).1.le, (hshift t ht).2⟩)
  have hFs (t : ℝ) (ht : t ∈ Ioo 0 delta) : ContDiff ℝ ∞ (F t) := by
    have hs := hws t ⟨ht.1.le, ht.2.le⟩
    exact (SmoothRadial.contDiff_even_norm hs.1 hs.2).exp.smul contDiff_id
  obtain ⟨hc, hd, hdd⟩ := composed_smooth_spatial_jets hFs hSs hS hF hDF hDDF
  let B : LeviCivitaData (intrinsicSpatialMetric (G.flow.metric t₀)
      (hrotation t₀ ⟨ht₀.1, ht₀.2.trans hTlt⟩)
      (G.complete P ⟨ht₀.1, ht₀.2.trans hTlt⟩)) :=
    Classical.choice (exists_leviCivitaData _)
  refine native_harmonic_map_joint_c2 (F := fun t => F t ∘ S t)
    (fun t => G.flow.connection (t₀ + t)) B isOpen_Ioo
    (fun t ht => (hFs t ht).comp (hSs t ht)) ?_ ?_ hc hd hdd ?_
  · exact ((rawConnectionCoefficient_family_contDiffOn G.flow).of_le (by simp)).comp
      (f := fun p : ℝ × StandardCapSpace => (t₀ + p.1, p.2))
      (hshiftMap.of_le (by simp)) hsmap'
  · intro i j
    exact ((raw_inverseGram_entry_family_contDiffOn G.flow i j).of_le (by simp)).comp
      (f := fun p : ℝ × StandardCapSpace => (t₀ + p.1, p.2))
      (hshiftMap.of_le (by simp)) hsmap'
  · intro t ht x
    let DI : LeviCivitaData (intrinsicSpatialMetric (G.flow.metric (t₀ + t))
        (hrotation (t₀ + t) ⟨(hshift t ht).1.le, (hshift t ht).2⟩)
        (G.complete P ⟨(hshift t ht).1.le, (hshift t ht).2⟩)) :=
      Classical.choice (exists_leviCivitaData _)
    have hs := hws t ⟨ht.1.le, ht.2.le⟩
    exact rawIntrinsicGaugeMap_solves_native_harmonic P G hrotation isOpen_Ioo hw
      ⟨ht₀.1, ht₀.2.trans hTlt⟩ ht (hshift t ht) hs.1 hs.2 (hPDE t ht) DI B x

end PoincareConjecture.M35.Uniqueness
