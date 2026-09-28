import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Inclusions








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Countable ι] {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (I : ι → MetricSurgeryInput K g)
  (R : ∀ i, MetricSurgeryResult g₀ (I i)) (U : Opens S.carrier) (hU : Nonempty U)
  (hd : Pairwise (fun i j => Disjoint ((I i).negativeHalf : Set S.carrier)
    ((I j).negativeHalf : Set S.carrier)))
  (hc : ∀ i, Disjoint (U : Set S.carrier) (I i).neck.central_sphere)

theorem cutMetric_pinched (D : LeviCivitaData g) (T : ℝ)
    (hp : SurgeryPinchedAt D T) (ht : ∀ i, (I i).time = T) :
    SurgeryPinchedAt (cutMetric I R U hU hd hc).leviCivitaData T := by
  let DQ := (cutMetric I R U hU hd hc).leviCivitaData
  have hbounds (q : (cutCarrier I R U hU hd hc).carrier) :
      -6 / (1 + 4 * T) ≤ DQ.scalarCurvature q ∧
      (0 < DQ.negativeCurvaturePart q →
        2 * DQ.negativeCurvaturePart q *
          (Real.log (DQ.negativeCurvaturePart q) + Real.log (1 + T) - 3) ≤
            DQ.scalarCurvature q) := by
    rcases cutCarrier_cover I R U hU hd hc q with ⟨x, rfl⟩ | ⟨i, x, rfl⟩
    · let DU := S.openSubsetConnection U g
      have hs : DQ.scalarCurvature (retainedInclusion I R U hU hd hc x) =
          D.scalarCurvature x.val :=
        (DU.scalarCurvature_eq_of_local_isometry DQ isOpen_univ
          (retainedInclusion_localDiffeomorph I R U hU hd hc).contMDiff.contMDiffOn
          (fun y _ a b => (retainedInclusion_metric I R U hU hd hc y a b).symm) (mem_univ x)).symm.trans
            (S.openSubset_scalar U g D x)
      have hn : DQ.negativeCurvaturePart (retainedInclusion I R U hU hd hc x) =
          D.negativeCurvaturePart x.val :=
        (MetricSurgery.negativeCurvaturePart_eq_of_local_isometry DU DQ isOpen_univ
          (retainedInclusion_localDiffeomorph I R U hU hd hc).contMDiff.contMDiffOn
          (fun y _ a b => (retainedInclusion_metric I R U hU hd hc y a b).symm) (mem_univ x)).symm.trans
            (S.openSubset_negativePart U g D x)
      rw [hs, hn]
      exact ⟨hp.2.1 x.val (mem_univ _), hp.2.2 x.val (mem_univ _)⟩
    · have hs := (R i).connection.scalarCurvature_eq_of_local_isometry DQ isOpen_univ
        (capInclusion_localDiffeomorph I R U hU hd hc i).contMDiff.contMDiffOn
        (fun y _ a b => (capInclusion_metric I R U hU hd hc i y a b).symm) (mem_univ x)
      have hn := MetricSurgery.negativeCurvaturePart_eq_of_local_isometry (R i).connection DQ
        isOpen_univ (capInclusion_localDiffeomorph I R U hU hd hc i).contMDiff.contMDiffOn
        (fun y _ a b => (capInclusion_metric I R U hU hd hc i y a b).symm) (mem_univ x)
      have hp' : SurgeryPinchedAt (R i).connection T := ht i ▸ (R i).pinched
      rw [← hs, ← hn]
      exact ⟨hp'.2.1 x (mem_univ _), hp'.2.2 x (mem_univ _)⟩
  exact ⟨hp.1, fun q _ => (hbounds q).1, fun q _ => (hbounds q).2⟩

end PoincareConjecture.Surgery.Terminal.Gluing
