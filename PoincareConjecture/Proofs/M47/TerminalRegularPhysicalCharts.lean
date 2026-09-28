import PoincareConjecture.Proofs.M47.TerminalSourcePhysicalComponent
import PoincareConjecture.Proofs.M47.TerminalCurvaturePartialInverse
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.SourceMetric
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.M13.OrdinaryFlow
import PoincareConjecture.Proofs.M13.ContractionTransport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)



theorem terminalSource_regular_component_scalar
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) (center : M)
    (DC : LeviCivitaData (RiemannianMetric.connectedComponentMetric
      (M13.scaleSmoothMetric g Q hQ) center))
    (z : Poincare.connectedComponentOpens E center) :
    DC.scalarCurvature z = D.scalarCurvature z.val / Q := by
  let h : RiemannianMetric 3 M := M13.scaleSmoothMetric g Q hQ
  let DH : LeviCivitaData h := h.leviCivitaData
  let C := Poincare.connectedComponentOpens E center
  have hscalar := DC.scalarCurvature_eq_of_local_isometry DH
    (f := (Subtype.val : C → M)) isOpen_univ
    (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) C).contMDiff.contMDiffOn
    (fun _ _ _ _ => rfl) (mem_univ z)
  exact hscalar.trans (M13.homothety_scalarCurvature_eq g h
    (Diffeomorph.refl (𝓡 3) M ∞) Q hQ
    (M13.identity_metricHomothety g Q hQ) D DH z.val)



theorem terminalSource_regular_physical_chart
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M]
    (U : ℕ → Opens E) [∀ i, Nonempty (U i)] (i : ℕ)
    (e : U i → M) (he : Topology.IsOpenEmbedding e)
    (hs : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ e) :
    let a := ChartDistance.chartParametrization
      (fun j => (U j : Set E)) (fun j => (U j).isOpen) e
    ∃ f : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞,
      (f : E → M) = a ∧ f.source = U i ∧ f.target = a '' (U i : Set E) := by
  let a := ChartDistance.chartParametrization
    (fun j => (U j : Set E)) (fun j => (U j).isOpen) e
  have ha : (fun x : U i => a x.val) = e := by
    funext x
    exact ChartDistance.chartParametrization_apply
      (fun j => (U j : Set E)) (fun j => (U j).isOpen) e x
  have hopen : Topology.IsOpenEmbedding (fun x : U i => a x.val) := ha ▸ he
  have hlocal : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ a (U i) := by
    intro x
    have hcomp : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (a ∘ (Subtype.val : U i → E)) x := by
      change IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (fun y : U i => a y.val) x
      rw [ha]
      exact hs x
    exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) (U i) x).of_comp hcomp
  exact terminalCurvature_exists_actual_partial_inverse (U i).isOpen hopen hlocal

end PoincareConjecture.M47
