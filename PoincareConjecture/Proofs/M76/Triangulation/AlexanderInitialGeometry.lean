import PoincareConjecture.Proofs.M76.Triangulation.AlexanderComplexityInitial
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveInduction
import PoincareConjecture.Proofs.M76.Triangulation.AlexanderInitialCollars
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialHeightSigns

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_initial_alexanderSectionProfile_with_collars
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) (hK : K.faces.Finite)
    (hA : InjOn A K.vertices)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2) :
    ∃ W : AlexanderSectionProfile E,
      W.carrier = K.space ∧ W.height = A ∧
      Function.support W.charge ⊆ A '' K.vertices ∧
      (A '' K.vertices).Finite ∧
      (∀ x ∈ W.carrier, A x ∉ A '' K.vertices →
        x ∈ closure (W.carrier ∩ {y | A y < A x}) ∧
          x ∈ closure (W.carrier ∩ {y | A x < A y})) ∧
      ∀ c : ℝ, W.charge c ≠ 0 →
        ∃ (m : ℕ) (n : Fin m → ℕ) (P : ∀ i, Polygon E (n i + 3)) (q : E),
          0 < m ∧ q ∈ K.vertices ∧ A q = c ∧
          (∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges) ∧
          K.space ∩ {x | A x = c} = ⋃ i, (P i).boundary ℝ ∧
          Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ {q}) ∧
          (¬ Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))) ∧
          alexanderCurveCount (fun i => (P i).boundary ℝ) = W.charge c ∧
          q ∈ closure ((K.space ∩ {x | A x = c}) \ {q}) ∧
          ∀ ε : ℝ, 0 < ε →
            ∃ β : ℝ, β ∈ Ioo 0 ε ∧ ∃ γ : ℝ, γ ∈ Ioo 0 ε ∧
              Nonempty (AlexanderHalfSlab K.space (A - AffineMap.const ℝ E c) q β) ∧
              Nonempty (AlexanderHalfSlab K.space (-(A - AffineMap.const ℝ E c)) q γ) := by
  classical
  obtain ⟨m, n, P, r, hP, hr, hresidue, hcover, hpair, _, hsupp, hfinite⟩ :=
    K.exists_finite_support_level_curve_families A hK hA hpure hcofaces
  let W : AlexanderSectionProfile E := {
    carrier := K.space
    height := A
    charge := fun c => alexanderCurveCount (fun i => (P c i).boundary ℝ)
    presentation := fun c =>
      ⟨m c, n c, P c, r c, hP c, hr c, hcover c, hpair c, rfl⟩
    finite_support := hfinite }
  obtain ⟨hevents, hsigns⟩ := K.finite_exceptional_vertex_height_signs hK A
  refine ⟨W, rfl, rfl, hsupp, hevents, hsigns, ?_⟩
  intro c hc
  have hbranch : ¬ Pairwise (fun i j =>
      Disjoint ((P c i).boundary ℝ) ((P c j).boundary ℝ)) := by
    intro hdisj
    exact hc ((alexanderCurveCount_eq_zero_iff _).mpr hdisj)
  have hmeet := hbranch
  change ¬ ∀ i j, i ≠ j → Disjoint ((P c i).boundary ℝ) ((P c j).boundary ℝ) at hmeet
  push Not at hmeet
  obtain ⟨i, j, hij, hijmeet⟩ := hmeet
  obtain ⟨q, hqi, hqj⟩ := not_disjoint_iff.mp hijmeet
  have hqr : q ∈ r c := hpair c hij ⟨hqi, hqj⟩
  obtain ⟨hqK, hqc⟩ := hresidue c hqr
  have hrq : r c = {q} := (hr c).eq_singleton_of_mem hqr
  have hqunion : q ∈ ⋃ k, (P c k).boundary ℝ := mem_iUnion.mpr ⟨i, hqi⟩
  have hfull : K.space ∩ {x | A x = c} = ⋃ k, (P c k).boundary ℝ := by
    rw [hcover c, hrq, union_eq_self_of_subset_left (singleton_subset_iff.mpr hqunion)]
  have hpairq : Pairwise (fun i j =>
      (P c i).boundary ℝ ∩ (P c j).boundary ℝ ⊆ {q}) := hrq ▸ hpair c
  have hacc : q ∈ closure ((K.space ∩ {x | A x = c}) \ {q}) :=
    Polygon.mem_closure_punctured_section_of_branching (n c) (P c) (hP c) q hpairq
      hbranch (fun k x hx => hfull.symm.subset (mem_iUnion.mpr ⟨k, hx⟩))
  refine ⟨m c, n c, P c, q, lt_of_le_of_lt (Nat.zero_le i.val) i.isLt,
    hqK, hqc, hP c, hfull, hpairq, hbranch, rfl, hacc, ?_⟩
  intro ε hε
  have haccq : q ∈ closure ((K.space ∩ {x | A x = A q}) \ {q}) := by
    rwa [hqc]
  have h := K.exists_small_generic_vertex_halfSlabs hK hpure A hA hqK haccq hε
  rwa [hqc] at h

end Geometry.SimplicialComplex
