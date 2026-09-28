import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Path
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.MorseReduction



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

namespace SphereSurgeryPath

variable {v : E3} {f g : S2 -> E3} (P : SphereSurgeryPath v f g)



theorem critical_mem_interior_core
    (hP : P.Protects ((fun p => inner Real v (f p)) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p = 0}))
    {p : S2} (hp : p ∈ P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p = 0) :
    p ∈ interior P.core := by
  by_contra hnot
  have hfront : p ∈ frontier P.core :=
    ⟨subset_closure hp, hnot⟩
  have hc0 := (P.mfderiv_eq_on_core p hp).symm.trans hc
  exact Set.disjoint_left.mp (P.disjoint_boundaryHeights hP)
    (P.frontier_height_mem p hfront) ⟨p, hc0, (P.height_eq_on_core hp).symm⟩

theorem regular_on_frontier_core
    (hP : P.Protects ((fun p => inner Real v (f p)) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p = 0})) :
    ∀ p ∈ frontier P.core,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p ≠ 0 := by
  intro p hp hc
  exact hp.2 (P.critical_mem_interior_core hP (P.isClosed_core.frontier_subset hp) hc)

end SphereSurgeryPath

namespace SphereMorseReduction

variable {f : S2 -> E3} (M : SphereMorseReduction f)



theorem subsingleton_critical_core {g : S2 -> E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g) :
    {p ∈ P.core | mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0}.Subsingleton := by
  obtain ⟨b, _, hband, _, hsingle⟩ := M.leaf_height_band hg
  intro p hp q hq
  apply hsingle
  · refine ⟨(P.mfderiv_eq_on_core p hp.1).symm.trans hp.2, ?_⟩
    have heq : inner Real (M.v : E3) (g p) = inner Real (M.v : E3) (M.D (f p)) :=
      P.height_eq_on_core hp.1
    rw [← heq]
    exact hband ⟨p, rfl⟩
  · refine ⟨(P.mfderiv_eq_on_core q hq.1).symm.trans hq.2, ?_⟩
    have heq : inner Real (M.v : E3) (g q) = inner Real (M.v : E3) (M.D (f q)) :=
      P.height_eq_on_core hq.1
    rw [← heq]
    exact hband ⟨q, rfl⟩



theorem exists_morse_chart_in_core {g : S2 -> E3}
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    {p : S2} (hp : p ∈ P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (g q)) p = 0) :
    ∃ (e : OpenPartialHomeomorph E2 S2) (σ : Fin 2 -> Real),
      (∀ i, σ i = -1 ∨ σ i = 1) ∧ 0 ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      e.target ⊆ interior P.core ∧
      ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
        inner Real (M.v : E3) (g p) + ∑ i : Fin 2, σ i * x i ^ 2 := by
  have hc0 := (P.mfderiv_eq_on_core p hp).symm.trans hc
  obtain ⟨e, σ, hσ, he0, hep, he, hei, hform⟩ := M.coordinates p hc0
  have hpint := P.critical_mem_interior_core hP hp hc
  let d := (e.symm.restrOpen (interior P.core) isOpen_interior).symm
  have hd0 : 0 ∈ d.source := ⟨he0, by change e 0 ∈ interior P.core; rw [hep]; exact hpint⟩
  refine ⟨d, σ, hσ, hd0, hep, he.mono inter_subset_left,
    hei.mono inter_subset_left, inter_subset_right, ?_⟩
  intro x hx
  have hxp : e x ∈ P.core := interior_subset hx.2
  have hheight : inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (M.D (f (e x))) := P.height_eq_on_core hxp
  have hheightp : inner Real (M.v : E3) (g p) =
      inner Real (M.v : E3) (M.D (f p)) := P.height_eq_on_core hp
  change inner Real (M.v : E3) (g (e x)) = _
  rw [hheight, hform x hx.1, hheightp]



theorem exists_terminal_core {g : S2 -> E3} (hg : g ∈ M.tree.leaves) :
    ∃ P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g,
      IsCompact P.core ∧
      {p ∈ P.core | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (g q)) p = 0}.Subsingleton ∧
      (∀ p ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (g q)) p = 0 -> p ∈ interior P.core) ∧
      ∀ p ∈ frontier P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (g q)) p ≠ 0 := by
  obtain ⟨P, hP⟩ := M.tree.exists_path_to_leaf hg M.protects_critical_values
  exact ⟨P, P.isClosed_core.isCompact, M.subsingleton_critical_core hg P,
    fun _ hp hc => P.critical_mem_interior_core hP hp hc,
    P.regular_on_frontier_core hP⟩

end SphereMorseReduction

end Poincare.Manifold.Schoenflies
