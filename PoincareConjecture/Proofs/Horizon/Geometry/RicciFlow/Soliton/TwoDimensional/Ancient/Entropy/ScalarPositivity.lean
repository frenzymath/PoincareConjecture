import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.ScalarEvolution.BoundaryRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.MaximumPrinciple.Positive
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.ScalarBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture

namespace RicciFlow

open Splitting.MaximumPrinciple

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem scalarCurvature_heatLowerContacts_surface {J : Set ℝ} (F : RicciFlow 2 M J) :
    HeatLowerContacts F.connection univ (interior J)
      (fun x t => (F.connection t).scalarCurvature x) := by
  intro x _ t ht ψ W hW hx hψ hψeq hψle
  let R := (F.connection t).scalarCurvature
  let d := (F.connection t).laplacian R x + (R x) ^ 2
  refine ⟨fun s => (F.connection s).scalarCurvature x, d,
    F.hasDerivAt_scalarCurvature_surface ht x, rfl,
    Eventually.of_forall (fun _ => le_rfl), ?_⟩
  have hR := (F.connection t).contMDiff_scalarCurvature
  have hmax : IsLocalMax (fun y => ψ y - R y) x := by
    filter_upwards [hψle] with y hy
    change ψ y - (F.connection t).scalarCurvature y ≤
      ψ x - (F.connection t).scalarCurvature x
    rw [hψeq]
    linarith
  have h := LeviCivitaData.Dirichlet.laplacian_nonpos_of_isLocalMax_on (F.connection t) hW
    (hψ.sub hR.contMDiffOn) hx hmax
  rw [LeviCivitaData.Dirichlet.laplacian_sub_on (F.connection t) hW hψ hR.contMDiffOn hx] at h
  dsimp only [d, R]
  nlinarith [sq_nonneg ((F.connection t).scalarCurvature x)]

theorem scalarCurvature_pos_surface_on_Icc [ConnectedSpace M]
    {a b : ℝ} (hab : a < b) (F : RicciFlow 2 M (Icc a b))
    (hoperator : ∀ t ∈ Icc a b, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hnonflat : ∃ x, (F.connection a).curvatureTensorNorm x ≠ 0) (q : M) :
    0 < (F.connection b).scalarCurvature q := by
  have hnonneg (t : ℝ) (ht : t ∈ Icc a b) (x : M) :
      0 ≤ (F.connection t).scalarCurvature x :=
    (F.connection t).scalar_nonnegative_of_nonnegative_curvatureOperator x
      (hoperator t ht x)
  obtain ⟨p, hp⟩ := hnonflat
  have hpos : 0 < (F.connection a).scalarCurvature p :=
    (F.connection a).scalar_positive_of_nonflat_surface p
      (hoperator a ⟨le_rfl, hab.le⟩ p) hp
  have hc : ContinuousOn (fun z : M × ℝ => (F.connection z.2).scalarCurvature z.1)
      (univ ×ˢ Icc a b) :=
    F.continuousOn_scalarCurvature_surface_Icc_swap hab
  have hcontacts := F.scalarCurvature_heatLowerContacts_surface
  rw [interior_Icc] at hcontacts
  exact positive_of_connected_on_Icc isOpen_univ isConnected_univ F.connection hab
    F.smooth hc hcontacts (fun x _ t ht => hnonneg t ht x)
    (mem_univ p) (mem_univ q) hpos

end RicciFlow

namespace AncientKappaSolution

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem scalarCurvature_pos_surface (K : AncientKappaSolution 2 M)
    (t : ℝ) (ht : t ≤ 0) (x : M) : 0 < (K.flow.connection t).scalarCurvature x := by
  have hab : t - 1 < t := by linarith
  have hsub : Icc (t - 1) t ⊆ Iic 0 := fun _ hs => hs.2.trans ht
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow K.flow hsub
    ordConnected_Icc ⟨t - 1, ⟨le_rfl, hab.le⟩, t, ⟨hab.le, le_rfl⟩, hab.ne⟩
  exact F.scalarCurvature_pos_surface_on_Icc hab
    (fun s hs => K.nonnegative_curvature_operator s (hsub hs))
    (K.nonflat (t - 1) (by linarith)) x

end AncientKappaSolution

end PoincareConjecture
