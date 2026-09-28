import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.BasedEventTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.FactorLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Event.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Class.Uniqueness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Diffeomorph

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M N : Type u}
  [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]
  [T2Space N] [SecondCountableTopology N]

theorem m67_based_width_le_of_distance_le
    (S : M59IdentificationSystem.{u}) (B : M59HigherBasepointTransportService.{u})
    (W : M61WidthTheory.{u} S.quotient)
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (hM : IsCompact (Set.univ : Set M)) (hN : IsCompact (Set.univ : Set N))
    (hcM : IsConnected (Set.univ : Set M)) (hcN : IsConnected (Set.univ : Set N))
    (x : M) (y : N)
    (hpM : Subsingleton (HomotopyGroup.Pi 2 M x))
    (hpN : Subsingleton (HomotopyGroup.Pi 2 N y))
    (f : C(M, N)) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (hbound : ∀ a b, h.edist (f a) (f b) ≤ g.edist a b)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x))
    (beta : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := N)) (constantC1Loop y))
    (hclass : M67AlphaTransport B x y f alpha beta) :
    m61BasedClassWidth S.quotient h y beta ≤ m61BasedClassWidth S.quotient g x alpha := by
  obtain ⟨L, p, lp, heq⟩ := hclass
  have hpre := W.based_class g hM hcM x hpM alpha
  have hpost := W.based_class h hN hcN y hpN beta
  have hnull : ∀ F : C(LoopTwoSphere, C1FreeLoopSpace (M := M)),
      M61NullFamily F → M61NullFamily (L.map.comp F) := by
    intro F hF c
    exact m67_null_transport_of_postcomposition f L (F c) (hF c)
  apply le_of_factor_sq_mul_forall_eta hpre.nonnegative
  intro eta heta
  refine m67_based_width_transport_of_rebased_family S.quotient g h x y alpha beta f L
    hpre hpost (W.family g hM)
    (fun F hF => W.free_class h hN _ (hnull F hF)) hnull
    (fun F hF hrep => ?_) eta heta ?_
  · refine ⟨L.map.comp F, hnull F hF, ?_, ContinuousMap.Homotopic.refl _⟩
    rw [← heq]
    exact m67_represents_postcomposition_rebase S B f hf L x y
      (S.core hN hcN y hpN) alpha lp.loop F hrep
  · intro F hF gamma D
    obtain ⟨E, hE⟩ := m67_filling_transport_of_lipschitz g h f hf L
      (L := 1) zero_le_one (fun a b => by simpa using hbound a b) gamma D
    refine ⟨E, hE.trans ?_⟩
    have hfac : (1 : ℝ) ≤ (1 + eta) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right (by simpa using hfac) D.area_nonnegative

theorem m67_based_width_eq_of_diffeomorph
    (S : M59IdentificationSystem.{u}) (B : M59HigherBasepointTransportService.{u})
    (W : M61WidthTheory.{u} S.quotient)
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N)
    (hM : IsCompact (Set.univ : Set M)) (hN : IsCompact (Set.univ : Set N))
    (hcM : IsConnected (Set.univ : Set M)) (hcN : IsConnected (Set.univ : Set N))
    (x : M) (y : N)
    (hpM : Subsingleton (HomotopyGroup.Pi 2 M x))
    (hpN : Subsingleton (HomotopyGroup.Pi 2 N y))
    (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (hinner : ∀ (z : M) (v w : TangentSpace (𝓡 3) z),
      g.inner z v w = h.inner (e z)
        (mfderiv (𝓡 3) (𝓡 3) e z v) (mfderiv (𝓡 3) (𝓡 3) e z w))
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x))
    (beta : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := N)) (constantC1Loop y))
    (hclass : M67AlphaTransport B x y (e.toHomeomorph : C(M, N)) alpha beta) :
    m61BasedClassWidth S.quotient h y beta = m61BasedClassWidth S.quotient g x alpha := by
  have hd := g.edist_diffeomorph h e hinner
  apply le_antisymm
  · exact m67_based_width_le_of_distance_le S B W g h hM hN hcM hcN x y hpM hpN
      (e.toHomeomorph : C(M, N)) e.contMDiff (fun a b => (hd a b).ge) alpha beta hclass
  · apply m67_based_width_le_of_distance_le S B W h g hN hM hcN hcM y x hpN hpM
      (e.symm.toHomeomorph : C(N, M)) e.symm.contMDiff
      (fun a b => ?_) beta alpha
      (m67_alpha_transport_symm S B e (S.core hM hcM x hpM) hclass)
    simpa using (hd (e.symm a) (e.symm b)).le

end PoincareConjecture
