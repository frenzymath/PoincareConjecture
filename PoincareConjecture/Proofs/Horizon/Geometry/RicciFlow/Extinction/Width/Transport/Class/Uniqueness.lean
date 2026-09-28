import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Class.Composition
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Rebasing.Represents

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology unitInterval

universe u

namespace PoincareConjecture

variable {M N : Type u}
  [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]

theorem m67_c1_loop_eq_of_extension_eq
    {a b : C1FreeLoopSpace (M := M)} (h : a.extension = b.extension) : a = b := by
  cases a with | mk f ext hf hreg hcont ht =>
    cases b with | mk g ext' hg hreg' hcont' ht' =>
      dsimp only at h
      cases h
      have hfg : f = g := funext (fun z => (hf z).symm.trans (hg z))
      cases hfg
      rfl

theorem m67_loop_postcomposition_map_unique {f : C(M, N)}
    (L K : M59LoopPostcomposition f) : L.map = K.map := by
  ext gamma
  apply m67_c1_loop_eq_of_extension_eq
  exact funext (fun z => (L.extension_agreement gamma z).trans
    (K.extension_agreement gamma z).symm)

theorem m67_represents_unique {q : M59SphereQuotient} {x : M}
    (C : M59IdentificationCore q x)
    {alpha beta : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)}
    {F : C(LoopTwoSphere, C1FreeLoopSpace (M := M))}
    (ha : M61Represents q x alpha F) (hb : M61Represents q x beta F) :
    alpha = beta := by
  obtain ⟨Gamma, hGamma, hclassGamma, hF⟩ := ha
  obtain ⟨Delta, hDelta, hclassDelta, hG⟩ := hb
  have h := (C.free_class_identification Gamma Delta hGamma hDelta).mp (hF.symm.trans hG)
  rw [hclassGamma, hclassDelta] at h
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2



theorem m67_alpha_transport_unique
    (S : M59IdentificationSystem.{u}) (B : M59HigherBasepointTransportService.{u})
    {x : M} {y : N} {f : C(M, N)} (hsmooth : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (CM : M59IdentificationCore S.quotient x)
    (CN : M59IdentificationCore S.quotient y)
    {alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)}
    {beta gamma : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := N)) (constantC1Loop y)}
    (hbeta : M67AlphaTransport B x y f alpha beta)
    (hgamma : M67AlphaTransport B x y f alpha gamma) : beta = gamma := by
  obtain ⟨L, p, lp, heq⟩ := hbeta
  obtain ⟨K, q, lq, heq'⟩ := hgamma
  obtain ⟨Gamma, hGamma, hclass⟩ := CM.regular_representatives alpha
  have hrep : M61Represents S.quotient x alpha (m59FamilyMap Gamma) :=
    ⟨Gamma, hGamma, hclass, ContinuousMap.Homotopic.refl _⟩
  have hrepL := m67_represents_postcomposition_rebase S B f hsmooth L x y CN alpha
    lp.loop _ hrep
  have hrepK := m67_represents_postcomposition_rebase S B f hsmooth K x y CN alpha
    lq.loop _ hrep
  rw [heq] at hrepL
  rw [heq'] at hrepK
  rw [m67_loop_postcomposition_map_unique L K] at hrepL
  exact m67_represents_unique CN hrepL hrepK

theorem m67_alpha_transport_exists
    (S : M59IdentificationSystem.{u}) (B : M59HigherBasepointTransportService.{u})
    (x : M) (y : N) (f : C(M, N)) (hsmooth : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (p : Path (f x) y)
    (alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)) :
    ∃ beta, M67AlphaTransport B x y f alpha beta := by
  obtain ⟨L⟩ := S.postcomposition f hsmooth
  exact ⟨_, L, p, m67ConstantLoopPath p, rfl⟩

theorem m67_alpha_transport_symm
    (S : M59IdentificationSystem.{u}) (B : M59HigherBasepointTransportService.{u})
    {x : M} {y : N} (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞)
    (CM : M59IdentificationCore S.quotient x)
    {alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := M)) (constantC1Loop x)}
    {beta : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := N)) (constantC1Loop y)}
    (h : M67AlphaTransport B x y (e.toHomeomorph : C(M, N)) alpha beta) :
    M67AlphaTransport B y x (e.symm.toHomeomorph : C(N, M)) beta alpha := by
  obtain ⟨L, p, lp, heq⟩ := h
  let q : Path (e.symm y) x :=
    (p.map e.symm.continuous).symm.cast rfl (e.symm_apply_apply x).symm
  obtain ⟨gamma, hgamma⟩ := m67_alpha_transport_exists S B y x
    (e.symm.toHomeomorph : C(N, M)) e.symm.contMDiff q beta
  have hcomp := m67_alpha_transport_trans B ⟨L, p, lp, heq⟩ hgamma
  have hid : (e.symm.toHomeomorph : C(N, M)).comp
      (e.toHomeomorph : C(M, N)) = ContinuousMap.id M := by
    ext z
    exact e.symm_apply_apply z
  rw [hid] at hcomp
  have heq' := m67_alpha_transport_unique S B contMDiff_id CM CM hcomp
    (m67_alpha_transport_refl B x alpha)
  exact heq' ▸ hgamma

end PoincareConjecture
