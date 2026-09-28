import PoincareConjecture.Proofs.M30.Thm11_1.TerminalComponentGeometry
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.MetricConvergence
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.M13.ContractionTransport

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

theorem terminalComponentMetric_scalarCurvature
    (S : GeneralizedBlowupSequence.{u}) (k : ℕ)
    (D : LeviCivitaData (terminalComponentMetric S k))
    (x : (terminalComponentCarrier S k).carrier) :
    D.scalarCurvature x =
      (S.flow k).scalar ⟨(S.base k).1, x.val⟩ / S.scale k := by
  let C := (S.flow k).slice (S.base k).1
  let g := (S.flow k).metric (S.base k).1
  let gscaled := M13.scaleSmoothMetric g (S.scale k) (S.base_scalar_pos k)
  let Dscaled := M13.scaleLeviCivitaData ((S.flow k).connection (S.base k).1)
    (S.scale k) (S.base_scalar_pos k)
  let i : (terminalComponentCarrier S k).carrier → C.carrier := Subtype.val
  have hi : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ i :=
    Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) _
  have hscalar : D.scalarCurvature x = Dscaled.scalarCurvature x.val :=
    D.scalarCurvature_eq_of_local_isometry Dscaled isOpen_univ hi.contMDiff.contMDiffOn
      (fun y _ v w => basedSliceMetric_inner C (S.base k).2 gscaled y v w)
      (mem_univ x)
  have hscale := M13.homothety_scalarCurvature_eq g gscaled
    (Diffeomorph.refl (𝓡 3) C.carrier ∞) (S.scale k) (S.base_scalar_pos k)
    (M13.identity_metricHomothety g (S.scale k) (S.base_scalar_pos k))
    ((S.flow k).connection (S.base k).1) Dscaled x.val
  exact hscalar.trans hscale

theorem terminalComponentMetric_base_scalar
    (S : GeneralizedBlowupSequence.{u}) (k : ℕ)
    (D : LeviCivitaData (terminalComponentMetric S k)) :
    D.scalarCurvature (terminalComponentBase S k) = 1 := by
  rw [terminalComponentMetric_scalarCurvature]
  change S.scale k / S.scale k = 1
  exact div_self (ne_of_gt (S.base_scalar_pos k))

theorem exists_eventually_terminal_source_compact_capture
    (S : GeneralizedBlowupSequence.{u})
    (G : PartialPointedMetricConvergence
      (terminalComponentMetric S) (terminalComponentBase S) 1)
    (hcover : ∀ R : ℝ, 0 < R → ∃ l : ℕ, ∀ᶠ k in atTop,
      (terminalComponentMetric S (G.subsequence k)).ball
        (terminalComponentBase S (G.subsequence k)) R ⊆
          G.embedding k '' G.exhaustion l) :
    ∀ R : ℝ, 0 < R → ∃ K : Set G.limitCarrier.carrier, IsCompact K ∧
      ∀ᶠ k in atTop, S.baseBall (G.subsequence k) R ⊆
        (fun x => (G.embedding k x).val) '' K := by
  intro R hR
  obtain ⟨l, hl⟩ := hcover R hR
  refine ⟨closure (G.exhaustion l), G.exhaustion_compactClosure l, ?_⟩
  filter_upwards [hl] with k hk x hx
  rw [← terminalComponentMetric_image_ball S (G.subsequence k) R] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨z, hz, rfl⟩ := hk hy
  exact ⟨z, subset_closure hz, rfl⟩

end PoincareConjecture.M30
