import PoincareConjecture.Proofs.M12.GeneralizedAtlas
import PoincareConjecture.Proofs.M11.OrdinaryChartHomeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M12

open PoincareConjecture.Proofs.M11

variable (F : GeneralizedRicciFlowData.{u})
  (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas F))

def originalBoxMap (b : F.box_index)
    (p : (R.timeIntervals.interval (boxInterval F b)).Point × (F.box b).carrier.carrier) :
    R.spacetime.Point := ⟨p.1.val, (F.box b).forward p.1.val p.1.property p.2⟩

theorem originalBoxMap_chart (b : F.box_index) (x : (F.box b).carrier.carrier)
    (q : (R.timeIntervals.interval (boxInterval F b)).Point × spatialChartDomain x) :
    originalBoxMap F R b (q.1, spatialChartInverse x q.2) =
      (R.boxCylinder ⟨b, x⟩).toSpacetime q :=
  (R.boxCylinder_eq ⟨b, x⟩ q).symm

theorem originalBoxMap_smooth (b : F.box_index) :
    ContMDiff (spacetimeModel 3) (spacetimeModel 3) ∞ (originalBoxMap F R b) := by
  intro p
  let e := spatialChartHomeomorph (n := 3) p.2
  have hp : p.2 ∈ e.target := by
    rw [spatialChartHomeomorph_target]
    exact mem_chart_source _ p.2
  have hi := (spatialChartHomeomorph_inverse_smooth p.2).contMDiffAt
    (e.open_target.mem_nhds hp)
  have hlocal := (R.boxCylinder ⟨b, p.2⟩).smooth.contMDiffAt.comp p
    (contMDiffAt_fst.prodMk (hi.comp p contMDiffAt_snd))
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [(e.open_target.preimage continuous_snd).mem_nhds hp] with q hq
  change originalBoxMap F R b q = (R.boxCylinder ⟨b, p.2⟩).toSpacetime (q.1, e.symm q.2)
  rw [← originalBoxMap_chart F R b p.2 (q.1, e.symm q.2)]
  change originalBoxMap F R b q = originalBoxMap F R b (q.1, e (e.symm q.2))
  rw [e.right_inv hq]

theorem originalBoxMap_derivative_chart (b : F.box_index)
    (x : (F.box b).carrier.carrier)
    (q : (R.timeIntervals.interval (boxInterval F b)).Point × spatialChartDomain x) :
    mfderiv (spacetimeModel 3) (spacetimeModel 3) (originalBoxMap F R b)
        (q.1, spatialChartInverse x q.2) ∘L
      mfderiv (spacetimeModel 3) (spacetimeModel 3)
        (Prod.map id (spatialChartInverse x)) q =
      mfderiv (spacetimeModel 3) (spacetimeModel 3)
        (R.boxCylinder ⟨b, x⟩).toSpacetime q := by
  have hj : ContMDiff (spacetimeModel 3) (spacetimeModel 3) ∞
      (Prod.map id (spatialChartInverse x) :
        (R.timeIntervals.interval (boxInterval F b)).Point × spatialChartDomain x →
        (R.timeIntervals.interval (boxInterval F b)).Point × (F.box b).carrier.carrier) :=
    contMDiff_fst.prodMk ((spatialChartInverse_smooth x).comp contMDiff_snd)
  have h := mfderiv_comp q
    ((originalBoxMap_smooth F R b _).mdifferentiableAt (by simp))
    ((hj q).mdifferentiableAt (by simp))
  have heq : originalBoxMap F R b ∘ Prod.map id (spatialChartInverse x) =
      (R.boxCylinder ⟨b, x⟩).toSpacetime := funext (originalBoxMap_chart F R b x)
  rw [heq] at h
  exact h.symm

theorem originalBoxMap_differential_injective (b : F.box_index)
    (p : (R.timeIntervals.interval (boxInterval F b)).Point × (F.box b).carrier.carrier) :
    Injective (mfderiv (spacetimeModel 3) (spacetimeModel 3) (originalBoxMap F R b) p) := by
  let x : spatialChartDomain (n := 3) p.2 :=
    ⟨chartAt (EuclideanSpace ℝ (Fin 3)) p.2 p.2, mem_chart_target _ p.2⟩
  have hx : spatialChartInverse p.2 x = p.2 :=
    (chartAt (EuclideanSpace ℝ (Fin 3)) p.2).left_inv (mem_chart_source _ p.2)
  have hj : Surjective (mfderiv (spacetimeModel 3) (spacetimeModel 3)
      (Prod.map id (spatialChartInverse p.2) :
        (R.timeIntervals.interval (boxInterval F b)).Point × spatialChartDomain p.2 →
        (R.timeIntervals.interval (boxInterval F b)).Point × (F.box b).carrier.carrier)
      (p.1, x)) := by
    rw [mfderiv_prodMap mdifferentiableAt_id
      ((spatialChartInverse_smooth p.2 x).mdifferentiableAt (by simp)), mfderiv_id]
    exact Surjective.prodMap (fun v => ⟨v, rfl⟩)
      ((spatialChartInverse_localDiffeomorph p.2 x).mfderivToContinuousLinearEquiv
        (by simp)).surjective
  have hc := (R.boxCylinder ⟨b, p.2⟩).differential_injective (p.1, x)
  rw [← originalBoxMap_derivative_chart F R b p.2 (p.1, x)] at hc
  change Injective ((mfderiv (spacetimeModel 3) (spacetimeModel 3)
    (originalBoxMap F R b) (p.1, spatialChartInverse p.2 x)) ∘
    (mfderiv (spacetimeModel 3) (spacetimeModel 3)
      (Prod.map id (spatialChartInverse p.2)) (p.1, x))) at hc
  have h := hc.of_comp_right hj
  have hp : (p.1, spatialChartInverse p.2 x) = p := Prod.ext rfl hx
  exact hp ▸ h

noncomputable def originalBoxCylinder (b : F.box_index) :
    CompatibleSpacetimeCylinder R.spacetime (R.timeIntervals.interval (boxInterval F b))
      (F.box b).carrier.carrier where
  interval_subset := by
    obtain ⟨U, _, hU⟩ := (F.box b).relatively_open
    change (F.box b).interval ⊆ F.interval
    rw [hU]
    exact inter_subset_left
  toSpacetime := originalBoxMap F R b
  embedding := (F.box_openEmbedding b).isEmbedding
  time_eq := fun _ => rfl
  worldline_smooth := by
    intro x
    exact (originalBoxMap_smooth F R b).comp (contMDiff_id.prodMk contMDiff_const)
  worldline_derivative := by
    intro t x
    let y : spatialChartDomain (n := 3) x :=
      ⟨chartAt (EuclideanSpace ℝ (Fin 3)) x x, mem_chart_target _ x⟩
    have hy : spatialChartInverse x y = x :=
      (chartAt (EuclideanSpace ℝ (Fin 3)) x).left_inv (mem_chart_source _ x)
    have heq : (fun s => originalBoxMap F R b (s, x)) =
        (fun s => (R.boxCylinder ⟨b, x⟩).toSpacetime (s, y)) := by
      funext s
      rw [← originalBoxMap_chart, hy]
    change mfderiv (𝓡∂ 1) (spacetimeModel 3) (fun s => originalBoxMap F R b (s, x)) t
      ((R.timeIntervals.interval (boxInterval F b)).positiveTangent t) = _
    rw [heq, congrFun heq t]
    exact (R.boxCylinder ⟨b, x⟩).worldline_derivative t y
  smooth := originalBoxMap_smooth F R b
  differential_injective := originalBoxMap_differential_injective F R b

end PoincareConjecture.Proofs.M12
