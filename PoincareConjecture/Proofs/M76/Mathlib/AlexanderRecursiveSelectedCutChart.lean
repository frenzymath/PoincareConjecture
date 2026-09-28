import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveBaseRestriction
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCollarSlab
import PoincareConjecture.Proofs.M76.Mathlib.CollarCutMembership
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineLevelComplex

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem AlexanderCollarSlab.exists_selected_cut_collar_chart
    {S s s' b : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs : IsClosed s) (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hinter : s ∩ s' ⊆ b) (hbs : b ⊆ s) (hbzero : b ⊆ {x | A x = 0})
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ b → (M.chart p : E) ∈ s)
    (Ks : SimplicialComplex ℝ E) (hKs : Ks.faces.Finite) (hKss : Ks.space = s) :
    ∃ C : {p : E × ℝ | p.1 ∈ s ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)} ≃ₜ (M.collar ∩ s : Set E), C.IsFinitePL ∧
      (∀ p : {p : E × ℝ | p.1 ∈ s ∩ {x | A x = 0} ∧
          p.2 ∈ Icc 0 (M.upper p.1)},
        (C p : E) = M.chart ⟨p,
          ⟨hunion.subset (Or.inl p.property.1.1), p.property.1.2⟩, p.property.2⟩) ∧
      (∀ p : {p : E × ℝ | p.1 ∈ s ∩ {x | A x = 0} ∧
          p.2 ∈ Icc 0 (M.upper p.1)}, A (C p) = (p : E × ℝ).2) ∧
      ∀ p : {p : E × ℝ | p.1 ∈ s ∩ {x | A x = 0} ∧
          p.2 ∈ Icc 0 (M.upper p.1)}, (C p : E) ∈ M.residual ∩ s ↔
        (p : E × ℝ).2 = M.upper (p : E × ℝ).1 := by
  have hTS : M.collar ⊆ S :=
    (subset_union_left.trans M.cover.subset).trans inter_subset_left
  have hfiber (p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
      p.2 ∈ Icc 0 (M.upper p.1)}) :
      (M.chart p : E) ∈ s ↔ (p : E × ℝ).1 ∈ s := by
    by_cases hpb : (p : E × ℝ).1 ∈ b
    · exact iff_of_true (hselected p hpb) (hbs hpb)
    · exact (M.chart.collar_fiber_mem_cut_iff M.height M.bottom hs hs'
        (hTS.trans hunion.symm.subset) hinter hbzero p hpb).1
  let B := s ∩ {x | A x = 0}
  have hB : B ⊆ S ∩ {x | A x = 0} :=
    fun _ hx => ⟨hunion.subset (Or.inl hx.1), hx.2⟩
  obtain ⟨K, hK, hKB⟩ := Ks.exists_finite_affineLevel_complex hKs A 0
  rw [hKss] at hKB
  obtain ⟨T, hT, C, hC, hCval, htest⟩ :=
    M.chart_finitePL.exists_collar_base_restriction M.width_pos
      (fun x hx => (M.upper_bounds x hx).2) hB K hK hKB
  have htarget : T = M.collar ∩ s := by
    apply Subset.antisymm
    · intro x hx
      let p := M.chart.symm ⟨x, hT hx⟩
      have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
      have hbase := (htest p).mp (hp.symm ▸ hx)
      exact ⟨hT hx, hp ▸ (hfiber p).mpr hbase.1⟩
    · intro x hx
      let p := M.chart.symm ⟨x, hx.1⟩
      have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
      have hbase : (p : E × ℝ).1 ∈ B :=
        ⟨(hfiber p).mp (hp.symm ▸ hx.2), p.property.1.2⟩
      exact hp ▸ (htest p).mpr hbase
  let D := (Homeomorph.setCongr (rfl : {p : E × ℝ | p.1 ∈ B ∧
      p.2 ∈ Icc 0 (M.upper p.1)} = _)).trans
    (C.trans (Homeomorph.setCongr htarget))
  refine ⟨D, hC.setCongr rfl htarget, hCval, ?_, ?_⟩
  · intro p
    change A (C p) = _
    rw [hCval]
    exact M.height _
  · intro p
    constructor
    · intro hp
      change (C p : E) ∈ M.residual ∩ s at hp
      rw [hCval] at hp
      exact (M.roof_contact _).mp hp.1
    · intro hp
      refine ⟨?_, (D p).property.2⟩
      change (C p : E) ∈ M.residual
      rw [hCval]
      exact (M.roof_contact _).mpr hp

end Geometry
