import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Flow.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Canonical.StaticCap
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Canonical.StaticComponents
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Assembly

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SurgeryCanonicalControl

theorem pullback_static_cover {F : SurgeryFlowData.{u}} {t epsilon C : ℝ}
    (S : GeneralizedSliceCarrier.{u}) (g : RiemannianMetric 3 S.carrier)
    (D : LeviCivitaData g)
    (e : Diffeomorph (𝓡 3) (𝓡 3) S.carrier (F.slice t).carrier ∞)
    (he : MetricHomothety g (F.metric t) e 1) (x : S.carrier)
    (h : SurgeryCanonicalControl F t (e x) epsilon C) :
    (∃ N : EpsilonNeck g, N.center = x ∧ N.epsilon = epsilon) ∨
    (∃ N : CapCertificate g, x ∈ N.core ∧ N.epsilon = epsilon ∧ N.cap_constant ≤ C) ∨
    (∃ U : Set S.carrier, x ∈ U ∧ U = connectedComponent x ∧
      ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 3) y,
        LeviCivitaData.IsOrthonormalPair g y v w → 0 < D.sectionalCurvature y v w) ∨
    (∃ N : SingularRoundComponent g epsilon, x ∈ N.carrier) := by
  have H : MetricHomothetyCalculus g (F.metric t) e 1 :=
    Homothety.metricHomothetyCalculus _ _ _ 1 (by norm_num) he
  cases h with
  | neck N hcenter =>
    left
    refine ⟨N.neck.m48_pullback he H D, ?_, N.epsilon_eq⟩
    change e.symm N.neck.center = x
    rw [hcenter, e.symm_apply_apply]
  | cap N hepsilon hconstant _ hcore =>
    exact Or.inr (Or.inl ⟨N.m48_pullback he H D, hcore, hepsilon, hconstant⟩)
  | component N hcontains =>
    let K := N.m48_pullback he H D
    have hx : x ∈ K.carrier := hcontains
    refine Or.inr (Or.inr (Or.inl ⟨K.carrier, hx, ?_, K.positive_sectional⟩))
    rw [K.component_eq] at hx ⊢
    exact connectedComponent_eq hx
  | round N hcontains =>
    exact Or.inr (Or.inr (Or.inr ⟨N.m48_pullback he, hcontains⟩))

end PoincareConjecture.SurgeryCanonicalControl
