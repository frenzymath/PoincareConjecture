import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Critical

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereMorseReduction

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private def swapMorseCoordinates : E2 ≃L[Real] E2 :=
  let C : E2 ≃L[Real] Real × Real := (EuclideanSpace.equiv (Fin 2) Real).trans
    (LinearEquiv.finTwoArrow Real Real).toContinuousLinearEquiv
  (C.trans (ContinuousLinearEquiv.prodComm Real Real Real)).trans C.symm

private theorem swapMorseCoordinates_zero (x : E2) : swapMorseCoordinates x 0 = x 1 := rfl
private theorem swapMorseCoordinates_one (x : E2) : swapMorseCoordinates x 1 = x 0 := rfl

variable {f : S2 → E3} (M : SphereMorseReduction f)

theorem terminal_core_cases
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0})) :
    (∀ p ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p ≠ 0) ∨
    (∃ p ∈ P.core, IsLocalMin (fun q => inner Real (M.v : E3) (g q)) p) ∨
    (∃ p ∈ P.core, IsLocalMax (fun q => inner Real (M.v : E3) (g q)) p) ∨
    ∃ p ∈ interior P.core,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (g q)) p = 0 ∧
      (∀ q ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (M.v : E3) (g y)) q = 0 → q = p) ∧
      ∃ e : OpenPartialHomeomorph E2 S2,
        0 ∈ e.source ∧ e 0 = p ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
        e.target ⊆ interior P.core ∧
        ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
          inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2 := by
  by_cases hreg : ∀ p ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p ≠ 0
  · exact Or.inl hreg
  push Not at hreg
  obtain ⟨p, hp, hc⟩ := hreg
  have hpi := P.critical_mem_interior_core hP hp hc
  have huniq : ∀ q ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y => inner Real (M.v : E3) (g y)) q = 0 → q = p :=
    fun q hq hqc => M.subsingleton_critical_core hg P ⟨hq, hqc⟩ ⟨hp, hc⟩
  obtain ⟨e, σ, hσ, he0, hep, he, hei, het, hform⟩ :=
    M.exists_morse_chart_in_core P hP hp hc
  have hpt : p ∈ e.target := hep ▸ e.map_source he0
  rcases hσ 0 with h0 | h0 <;> rcases hσ 1 with h1 | h1
  · refine Or.inr (Or.inr (Or.inl ⟨p, hp, ?_⟩))
    show ∀ᶠ q in 𝓝 p, inner Real (M.v : E3) (g q) ≤ inner Real (M.v : E3) (g p)
    filter_upwards [e.open_target.mem_nhds hpt] with q hq
    have hh := hform (e.symm q) (e.map_target hq)
    rw [e.right_inv hq, Fin.sum_univ_two, h0, h1] at hh
    nlinarith [sq_nonneg ((e.symm q) 0), sq_nonneg ((e.symm q) 1)]
  · refine Or.inr (Or.inr (Or.inr ⟨p, hpi, hc, huniq,
      e, he0, hep, he, hei, het, ?_⟩))
    intro x hx
    rw [hform x hx, Fin.sum_univ_two, h0, h1]
    ring
  · let C := swapMorseCoordinates
    let d := C.toHomeomorph.toOpenPartialHomeomorph.trans e
    have hd0 : (0 : E2) ∈ d.source := ⟨mem_univ _, by simpa using he0⟩
    have hdp : d 0 = p := by change e (C 0) = p; simpa using hep
    have hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source :=
      he.comp C.contDiff.contMDiff.contMDiffOn (fun x hx => hx.2)
    have hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target :=
      C.symm.contDiff.contMDiff.comp_contMDiffOn (hei.mono (fun x hx => hx.1))
    have hdt : d.target ⊆ interior P.core := fun x hx => het hx.1
    refine Or.inr (Or.inr (Or.inr ⟨p, hpi, hc, huniq,
      d, hd0, hdp, hd, hdi, hdt, ?_⟩))
    intro x hx
    change inner Real (M.v : E3) (g (e (C x))) = _
    rw [hform (C x) hx.2, Fin.sum_univ_two, h0, h1]
    change inner Real (M.v : E3) (g p) +
      (1 * swapMorseCoordinates x 0 ^ 2 + -1 * swapMorseCoordinates x 1 ^ 2) = _
    rw [swapMorseCoordinates_zero, swapMorseCoordinates_one]
    ring
  · refine Or.inr (Or.inl ⟨p, hp, ?_⟩)
    show ∀ᶠ q in 𝓝 p, inner Real (M.v : E3) (g p) ≤ inner Real (M.v : E3) (g q)
    filter_upwards [e.open_target.mem_nhds hpt] with q hq
    have hh := hform (e.symm q) (e.map_target hq)
    rw [e.right_inv hq, Fin.sum_univ_two, h0, h1] at hh
    nlinarith [sq_nonneg ((e.symm q) 0), sq_nonneg ((e.symm q) 1)]

end Poincare.Manifold.Schoenflies.SphereMorseReduction
