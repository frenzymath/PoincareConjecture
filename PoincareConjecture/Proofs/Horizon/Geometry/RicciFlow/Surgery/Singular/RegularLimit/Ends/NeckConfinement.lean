import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.CapConfinement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Curvature








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.TerminalEnd



theorem exists_neck_confinement_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (E : GeneralizedFlowExtension F T) (K : TerminalComponentPath E)
        (e : TerminalEnd K) {epsilon : ℝ}, epsilon ≤ ε₀ →
        (∃ L : ℝ, ∀ x, L ≤ (E.extended.connection T).scalarCurvature x) →
        (∀ D : Set ℝ, IsCompact D →
          IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' D)) →
        ∀ k : ℕ, ∀ L : Set (E.extended.slice T).carrier, IsCompact L →
          ∃ n : ℕ, k ≤ n ∧ ∀ m : ℕ, n ≤ m → ∀ x ∈ e.tail m,
            ∀ N : TerminalStrongNeck E epsilon, N.center = x.val →
              N.carrier ⊆ Subtype.val '' e.tail k ∧ Disjoint N.carrier L := by
  obtain ⟨ε₀, hε₀, hsmall, hscalar⟩ := GeneralizedStrongNeck.exists_scalar_control.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro F T E K e epsilon hε hlower hproper k L hL
  let D := E.extended.connection T
  let J := L ∪ Subtype.val '' (e.exhaustion k : Set K.component)
  have hJ : IsCompact J :=
    hL.union ((e.exhaustion.isCompact k).image continuous_subtype_val)
  obtain ⟨B, hB⟩ := hJ.bddAbove_image D.continuous_scalarCurvature.continuousOn
  obtain ⟨n, hn⟩ := e.exists_tail_scalar_gt hlower hproper (2 * max B 0)
  refine ⟨max k n, le_max_left _ _, fun m hnm x hx N hcenter => ?_⟩
  have hhigh : 2 * max B 0 < D.scalarCurvature x :=
    hn m ((le_max_right _ _).trans hnm) x hx
  have havoid : Disjoint N.carrier J := by
    rw [Set.disjoint_left]
    intro y hyN hyJ
    have hcompare := (hscalar N hε y hyN).1
    rw [hcenter] at hcompare
    have hupper := (hB ⟨y, hyJ, rfl⟩).trans (le_max_left B 0)
    change D.scalarCurvature x / 2 < D.scalarCurvature y at hcompare
    linarith
  refine ⟨?_, havoid.mono_right subset_union_left⟩
  apply e.subset_tail_image_of_isPreconnected k N.isPreconnected_carrier
    (havoid.mono_right subset_union_right) (e.nested ((le_max_left _ _).trans hnm) hx)
  rw [← hcenter]
  exact N.central_sphere_subset N.center_on_central_sphere

end PoincareConjecture.TerminalEnd
