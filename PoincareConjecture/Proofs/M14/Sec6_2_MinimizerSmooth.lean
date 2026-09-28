import PoincareConjecture.Proofs.M14.Sec6_2_MinimizerCoordinates
import PoincareConjecture.Proofs.M14.Sec6_2_OpenFieldExtension

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)

theorem minimizing_curve_contMDiffOn (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hmin : M14IsMinimizing p) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ p.curve (Ioo τ₁ τ₂) := by
  intro t ht
  obtain ⟨b, U, lift, hU, htU, hlift, hright, _⟩ := exists_smooth_gauge_lift G (p.curve t)
  let J := Ioo τ₁ τ₂ ∩ p.curve ⁻¹' U
  have hJ : IsOpen J := p.curve_regular.continuousOn.isOpen_inter_preimage isOpen_Ioo hU
  have htJ : t ∈ J := ⟨ht, htU⟩
  obtain ⟨a, c, htac, hacN, hacJ⟩ := exists_Icc_mem_subset_of_mem_nhds (hJ.mem_nhds htJ)
  have hac : a < c := (Icc_mem_nhds_iff.mp hacN).1.trans (Icc_mem_nhds_iff.mp hacN).2
  have hu := (minimizing_gaugeCoordinate_regularity p b lift (lift (p.curve t)).2 hM12 hmin
    hU hlift hright hJ inter_subset_left (fun _ hs => hs.2) hac hacJ).1
  have hs : ContMDiffWithinAt (𝓘(ℝ, ℝ)) (𝓡 n) ∞
      (fun s => (lift (p.curve s)).2) (Icc a c) t :=
    (ContMDiffWithinAt.subtypeVal_comp_iff (G.gaugeCover.spatial b) _ _ t).mp
      (hu.contMDiffOn t htac)
  have hθ := gaugeLift_time_contMDiffOn p b lift hright
    (show J ⊆ Icc τ₁ τ₂ from inter_subset_left.trans Ioo_subset_Icc_self)
    (fun _ hs => hs.2)
  have hpair := ((hθ t htJ).contMDiffAt (hJ.mem_nhds htJ)).prodMk (hs.contMDiffAt hacN)
  have hcyl := (G.gaugeCover.cylinder b).smooth.contMDiffAt.comp t hpair
  have heq : p.curve =ᶠ[𝓝 t]
      (fun s => (G.gaugeCover.cylinder b).toSpacetime (lift (p.curve s))) := by
    filter_upwards [hJ.mem_nhds htJ] with s hs
    exact (hright _ hs.2).symm
  exact (hcyl.congr_of_eventuallyEq heq).contMDiffWithinAt

theorem minimizing_horizontalVelocity_contMDiffOn (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hmin : M14IsMinimizing p) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) (p.curve s) (p.horizontal_velocity s)) (Ioo τ₁ τ₂) := by
  have hv := projectedCurveVelocityWithin_smooth isOpen_Ioo.uniqueDiffOn
    (minimizing_curve_contMDiffOn p hM12 hmin)
  apply hv.congr
  intro s hs
  simp only [backwardPath_velocity_eq_projected p hs, projectedCurveVelocityWithin,
    projectedCurveVelocity, mfderivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hs)]

theorem exists_minimizing_velocity_extension (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hmin : M14IsMinimizing p) :
    Nonempty (M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity) :=
  exists_pullbackExtension_of_isOpen isOpen_Ioo
    (minimizing_horizontalVelocity_contMDiffOn p hM12 hmin)

end PoincareConjecture.M14
