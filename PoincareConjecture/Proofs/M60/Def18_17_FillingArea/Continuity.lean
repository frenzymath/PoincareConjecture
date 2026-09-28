import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.BoundaryRegularization
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.DiskExistence
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.ParametrizedContinuity
import PoincareConjecture.Statements.M60Area










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]




theorem m60FillingArea_parametrized_near_minimizer (g : RiemannianMetric 3 M)
    (gamma : C1FreeLoopSpace (M := M)) (hnull : IsNullHomotopicLoop gamma)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ D : LipschitzSpanningDisk g gamma,
      (∀ z : LoopCircle, D.map z = gamma z) ∧ D.area < fillingArea g gamma + epsilon := by
  obtain ⟨D⟩ := m60_exists_lipschitz_disk_of_null g gamma hnull
  obtain ⟨E, hE⟩ := m60FillingArea_near_minimizer_of_disk g gamma D hepsilon
  obtain ⟨E', hboundary, harea⟩ := m60Disk_regularize_boundary g E
  exact ⟨E', hboundary, harea.trans_lt hE⟩



theorem m60FillingArea_continuousOn (g : RiemannianMetric 3 M)
    (hcompact : IsCompact (univ : Set M)) :
    ContinuousOn (fun gamma : C1FreeLoopSpace (M := M) => fillingArea g gamma)
      {gamma | IsNullHomotopicLoop gamma} :=
  m60FillingArea_continuousOn_of_parametrized_near_minimizers g hcompact
    (m60FillingArea_parametrized_near_minimizer g)



theorem m60FillingAreaProperties_of_compact (g : RiemannianMetric 3 M)
    (hcompact : IsCompact (univ : Set M)) : M60FillingAreaProperties g where
  filling_data := m60FillingData_of_null g
  nonnegative := by
    intro gamma hnull
    obtain ⟨D⟩ := m60_exists_lipschitz_disk_of_null g gamma hnull
    exact m60FillingArea_nonneg_of_disk g gamma D
  near_minimizer := by
    intro gamma hnull epsilon hepsilon
    obtain ⟨D, _, harea⟩ :=
      m60FillingArea_parametrized_near_minimizer g gamma hnull epsilon hepsilon
    exact ⟨D, harea⟩
  reparameterization := fun _ _ h => m60FillingArea_eq_of_reparameterized g h
  continuous_on_null_loops := m60FillingArea_continuousOn g hcompact

end PoincareConjecture
