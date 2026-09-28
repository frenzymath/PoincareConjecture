import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable (T : OpenPartialHomeomorph (E2 × ℝ) E3)
variable (h : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
variable (g : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)

noncomputable def heightTransportTube : OpenPartialHomeomorph (E2 × ℝ) E3 :=
  (((Homeomorph.refl E2).prodCongr h.symm.toHomeomorph).toOpenPartialHomeomorph.trans T).trans
    g.toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem heightTransportTube_apply (p : E2 × ℝ) :
    heightTransportTube T h g p = g (T (p.1, h.symm p.2)) := rfl

@[simp] theorem heightTransportTube_symm_apply (y : E3) :
    (heightTransportTube T h g).symm y =
      ((T.symm (g.symm y)).1, h (T.symm (g.symm y)).2) := rfl

theorem heightTransportTube_mem_source (p : E2 × ℝ) :
    p ∈ (heightTransportTube T h g).source ↔ (p.1, h.symm p.2) ∈ T.source := by
  change ((True ∧ (p.1, h.symm p.2) ∈ T.source) ∧ True) ↔ _
  simp only [true_and, and_true]

theorem heightTransportTube_mem_target (y : E3) :
    y ∈ (heightTransportTube T h g).target ↔ g.symm y ∈ T.target := by
  change (True ∧ g.symm y ∈ T.target ∧ True) ↔ _
  simp only [true_and, and_true]

theorem heightTransportTube_contDiffOn (hT : ContDiffOn ℝ ∞ T T.source) :
    ContDiffOn ℝ ∞ (heightTransportTube T h g) (heightTransportTube T h g).source := by
  have hP : ContDiff ℝ ∞ (fun p : E2 × ℝ => (p.1, h.symm p.2)) :=
    contDiff_fst.prodMk (h.symm.contDiff.comp contDiff_snd)
  exact g.contDiff.comp_contDiffOn (hT.comp hP.contDiffOn
    (fun p hp => (heightTransportTube_mem_source T h g p).mp hp))

theorem heightTransportTube_contDiffOn_symm
    (hT : ContDiffOn ℝ ∞ T.symm T.target) :
    ContDiffOn ℝ ∞ (heightTransportTube T h g).symm
      (heightTransportTube T h g).target := by
  have hP : ContDiff ℝ ∞ (fun p : E2 × ℝ => (p.1, h p.2)) :=
    contDiff_fst.prodMk (h.contDiff.comp contDiff_snd)
  exact hP.comp_contDiffOn (hT.comp g.symm.contDiff.contDiffOn
    (fun y hy => (heightTransportTube_mem_target T h g y).mp hy))

theorem heightTransportTube_closedDisc_source
    (hT : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source) :
    closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (heightTransportTube T h g).source := by
  intro p hp
  exact (heightTransportTube_mem_source T h g p).mpr (hT ⟨hp.1, mem_univ _⟩)

theorem heightTransportTube_height (u v : UnitTwoSphere)
    (hT : ∀ p ∈ T.source, ⟪(u : E3), T p⟫_ℝ = p.2)
    (hg : ∀ y : E3, ⟪(v : E3), g y⟫_ℝ = h ⟪(u : E3), y⟫_ℝ)
    (p : E2 × ℝ) (hp : p ∈ (heightTransportTube T h g).source) :
    ⟪(v : E3), heightTransportTube T h g p⟫_ℝ = p.2 := by
  rw [heightTransportTube_apply, hg,
    hT _ ((heightTransportTube_mem_source T h g p).mp hp)]
  exact h.apply_symm_apply p.2

theorem heightTransportTube_reparametrized_apply (p : E2 × ℝ) :
    heightTransportTube T h g (p.1, h p.2) = g (T p) := by
  rw [heightTransportTube_apply, h.symm_apply_apply]

end PoincareConjecture.M25.Topology3D
