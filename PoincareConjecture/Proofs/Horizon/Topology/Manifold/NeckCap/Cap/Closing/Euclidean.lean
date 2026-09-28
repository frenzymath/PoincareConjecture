import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.EuclideanMatching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Certificate
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts.MatchingBalls











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}



theorem nonempty_two_euclidean_cap_closedComponentCertificate (C D : CapCertificate g)
    (hC : C.model_kind = .euclidean) (hD : D.model_kind = .euclidean)
    (hcompact : IsCompact (C.carrier ∪ D.carrier))
    (hcomponent : ∃ x : M, C.carrier ∪ D.carrier = connectedComponent x) :
    Nonempty (ClosedComponentCertificate .threeSphere (C.carrier ∪ D.carrier)) := by
  classical
  obtain ⟨r, b₀, b₁, hr, _, _, _, hb₀, hbi₀, hb₁, hbi₁, hs₀, hs₁,
    ht₀, ht₁, _, hcover, hintersection, hmatch⟩ :=
    C.exists_two_cap_euclidean_matching_balls D hC hD hcompact
  let U : TopologicalSpace.Opens M := ⟨C.carrier ∪ D.carrier, C.carrier_open.union D.carrier_open⟩
  have hU : Nonempty U := by
    obtain ⟨x, hx⟩ := hcomponent
    exact ⟨⟨x, hx.symm.subset mem_connectedComponent⟩⟩
  obtain ⟨d⟩ := SphereCharts.nonempty_diffeomorph_of_matching_balls_in_open U hU
    b₀ b₁ hr hs₀ hs₁ ht₀ ht₁ hb₀ hb₁ hbi₀ hbi₁ hcover hintersection hmatch
  let inv : M → U := fun x => if hx : x ∈ U then ⟨x, hx⟩ else Classical.choice hU
  have hinv (x : M) (hx : x ∈ U) : (inv x : M) = x := by simp [inv, hx]
  have hinv_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inv (U : Set M) := by
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U inv (U : Set M) x).mp
    apply contMDiffWithinAt_id.congr
    · intro y hy
      exact hinv y hy
    · exact hinv x hx
  let S : SmoothClosedComponentModel .threeSphere (C.carrier ∪ D.carrier) := {
    model := U
    model_topology := inferInstance
    model_charted := inferInstance
    model_manifold := inferInstance
    standard_model := d.toHomeomorph
    standard_smooth := ⟨d⟩
    forward := Subtype.val
    inverse := inv
    forward_mem := fun x => x.property
    left_inverse := hinv
    right_inverse := fun x => Subtype.ext (hinv x x.property)
    forward_smooth := contMDiff_subtype_val
    inverse_smooth := hinv_smooth }
  exact S.nonempty_closedComponentCertificate hcompact hcomponent

end PoincareConjecture.CapCertificate
