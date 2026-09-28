import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_OpenCoordinateRicci
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactEnergy
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.OpenDomain











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem exists_metric_of_open_coefficients {n : ℕ} (U : Opens (E n))
    (B : E n → SpacetimeBounds.MetricCoefficient n)
    (hsmooth : ContDiffOn ℝ ∞ B U)
    (hsymm : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (hpos : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < B x v v) :
    ∃ g : RiemannianMetric n U,
      ∀ (x : U) (v w : TangentSpace (𝓡 n) x), g.inner x v w = B x v w := by
  apply RiemannianMetric.exists_of_coordinate_limit U (fun _ => B) B hsmooth
    (fun _ => hsymm) (fun _ _ _ _ => tendsto_const_nhds)
  intro x hx
  obtain ⟨c, hc, hbound⟩ := exists_uniform_bilinear_lower_bound
    (isCompact_singleton (x := x))
    (hsmooth.continuousOn.mono (singleton_subset_iff.mpr hx))
    (fun y hy => hpos y ((singleton_subset_iff.mpr hx) hy))
  exact ⟨c, hc, Eventually.of_forall (fun _ => hbound x (mem_singleton x))⟩




theorem open_metric_family_smooth {n : ℕ} (U : Opens (E n))
    (g : ℝ → RiemannianMetric n U) {J : Set ℝ}
    (B : ℝ × E n → SpacetimeBounds.MetricCoefficient n)
    (hB : ContDiffOn ℝ ∞ B (J ×ˢ U))
    (hcoeff : ∀ t ∈ J, ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
      (g t).inner x v w = B (t, x) v w) :
    RiemannianMetric.IsSmoothFamilyOn g J := by
  apply RiemannianMetric.isSmoothFamilyOn_of_constant_chart
    (fun _ _ => by simp [Opens.chartAt_eq]) g (fun p => B (p.1, p.2)) _ hcoeff
  have hmap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ × E n) ∞
      (fun p : ℝ × U => (p.1, (p.2 : E n))) :=
    contMDiff_fst.prodMk_space (contMDiff_subtype_val.comp contMDiff_snd)
  exact hB.contMDiffOn.comp hmap.contMDiffOn (fun p hp => ⟨hp.1, p.2.property⟩)




theorem exists_ricciFlow_of_open_coefficients {n : ℕ} (U : Opens (E n))
    {J : Set ℝ} (hJ : J.OrdConnected) (hne : J.Nontrivial)
    (B : ℝ × E n → SpacetimeBounds.MetricCoefficient n)
    (hspace : ∀ t, ContDiffOn ℝ ∞ (fun x => B (t, x)) U)
    (hsymm : ∀ t, ∀ x ∈ U, ∀ v w, B (t, x) v w = B (t, x) w v)
    (hpos : ∀ t, ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < B (t, x) v v)
    (hsmooth : ContDiffOn ℝ ∞ B (J ×ˢ U))
    (hevol : ∀ t ∈ J, ∀ x ∈ U,
      HasDerivWithinAt (fun s => B (s, x))
        (SpacetimeBounds.ricciFlowOperator n
          (SpacetimeBounds.metricTwoJet (fun y => B (t, y)) x)) J t) :
    ∃ F : RicciFlow n U J,
      ∀ t, ∀ (x : U) (v w : TangentSpace (𝓡 n) x),
        (F.metric t).inner x v w = B (t, x) v w := by
  classical
  choose g hcoeff using fun t =>
    exists_metric_of_open_coefficients U (fun x => B (t, x)) (hspace t) (hsymm t) (hpos t)
  let D : ∀ t, LeviCivitaData (g t) := fun t => (g t).openEuclideanLeviCivitaData U
  refine ⟨{
    metric := g
    connection := D
    interval := hJ
    nontrivial := hne
    smooth := open_metric_family_smooth U g B hsmooth (fun t _ => hcoeff t)
    equation := ?_ }, hcoeff⟩
  intro t ht x v w
  have hd : HasDerivWithinAt (fun s => B (s, x) v w)
      (SpacetimeBounds.ricciFlowOperator n
        (SpacetimeBounds.metricTwoJet (fun y => B (t, y)) x) v w) J t := by
    simpa using ((hevol t ht x x.2).clm_apply
      (hasDerivWithinAt_const t J (show E n from v))).clm_apply
        (hasDerivWithinAt_const t J (show E n from w))
  rw [ricciFlowOperator_open_coefficients U (D t) (hcoeff t)] at hd
  simpa only [hcoeff] using hd

end PoincareConjecture.M44
