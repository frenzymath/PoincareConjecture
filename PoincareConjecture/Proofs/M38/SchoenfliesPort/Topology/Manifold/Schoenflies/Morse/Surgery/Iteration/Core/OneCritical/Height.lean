import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.AuxiliaryHeight
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Critical







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

namespace SphereMorseReduction

variable {f : S2 → E3} (M : SphereMorseReduction f)




theorem exists_auxiliary_height_with_unique_critical_point
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    {B : Set Real} (L : List (SphereSurgeryCoreCap (M.v : E3) g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    (hcore : P.core = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    {p : S2} (hp : p ∈ P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (a b : Real) (hpband : inner Real (M.v : E3) (g p) ∈ Icc a b) :
    ∃ h : S2 → Real,
      ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h ∧
      (∀ q ∈ P.core, h =ᶠ[𝓝 q] (fun r => inner Real (M.v : E3) (g r))) ∧
      {q | h q ∈ Icc a b ∧ mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0} = {p} ∧
      (∀ D ∈ L, ∀ q ∈ D.chart '' ball 0 1,
        (inner Real (M.v : E3) (g q) - D.center) / D.scale < 1 / 4 →
          h =ᶠ[𝓝 q] (fun r => inner Real (M.v : E3) (g r))) ∧
      ∃ (e : OpenPartialHomeomorph E2 S2) (σ : Fin 2 → Real),
        (∀ i, σ i = -1 ∨ σ i = 1) ∧ 0 ∈ e.source ∧ e 0 = p ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
        e.target ⊆ interior P.core ∧
        (∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
          inner Real (M.v : E3) (g p) + ∑ i : Fin 2, σ i * x i ^ 2) ∧
        ∀ x ∈ e.source, h (e x) = h p + ∑ i : Fin 2, σ i * x i ^ 2 := by
  obtain ⟨h, hh, hactual, hcrit, hlow⟩ :=
    SphereSurgeryCoreCap.exists_auxiliary_height_preserving_core_critical_points
      L hpair (M.tree.embedding_of_mem_leaves hg) hcore a b
  have hsingle := M.subsingleton_critical_core hg P
  have hcritical :
      {q | h q ∈ Icc a b ∧ mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0} = {p} := by
    ext q
    constructor
    · rintro ⟨hqband, hqc⟩
      exact hsingle ((hcrit q hqband).mp hqc) ⟨hp, hc⟩
    · intro hqp
      have hqp' : q = p := hqp
      subst q
      refine ⟨?_, (hactual p hp).mfderiv_eq.trans hc⟩
      rwa [(hactual p hp).eq_of_nhds]
  obtain ⟨e, σ, hσ, he0, hep, he, hei, het, hform⟩ :=
    M.exists_morse_chart_in_core P hP hp hc
  refine ⟨h, hh, hactual, hcritical, hlow, e, σ, hσ, he0, hep, he, hei, het, hform, ?_⟩
  intro x hx
  rw [(hactual (e x) (interior_subset (het (e.map_source hx)))).eq_of_nhds,
    (hactual p hp).eq_of_nhds]
  exact hform x hx



theorem exists_auxiliary_height_of_critical_core
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (a b : Real) (hpband : inner Real (M.v : E3) (g p) ∈ Icc a b) :
    ∃ h : S2 → Real,
      ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h ∧
      (∀ q ∈ P.core, h =ᶠ[𝓝 q] (fun r => inner Real (M.v : E3) (g r))) ∧
      {q | h q ∈ Icc a b ∧ mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0} = {p} ∧
      ∃ (e : OpenPartialHomeomorph E2 S2) (σ : Fin 2 → Real),
        (∀ i, σ i = -1 ∨ σ i = 1) ∧ 0 ∈ e.source ∧ e 0 = p ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
        e.target ⊆ interior P.core ∧
        (∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
          inner Real (M.v : E3) (g p) + ∑ i : Fin 2, σ i * x i ^ 2) ∧
        ∀ x ∈ e.source, h (e x) = h p + ∑ i : Fin 2, σ i * x i ^ 2 := by
  obtain ⟨L, hpair, hcore⟩ := P.exists_model_cap_complement hcaps hP
  obtain ⟨h, hh, hactual, hcritical, _, hcoordinates⟩ :=
    M.exists_auxiliary_height_with_unique_critical_point hg P hP L hpair hcore hp hc a b hpband
  exact ⟨h, hh, hactual, hcritical, hcoordinates⟩

end SphereMorseReduction

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
