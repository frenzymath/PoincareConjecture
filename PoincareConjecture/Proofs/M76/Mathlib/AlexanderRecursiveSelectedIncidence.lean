import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCollarSlab
import PoincareConjecture.Proofs.M76.Mathlib.CollarCutMembership

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem AlexanderCollarSlab.selected_collar_decomposition
    {S s s' b k d TX TY : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs : IsClosed s) (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hinter : s ∩ s' ⊆ b) (hB : S ∩ {x | A x = 0} = b ∪ k)
    (htouch : b ∩ k ⊆ {q}) (hqs : q ∈ s)
    (hcap : d ∩ S = b)
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ b → (M.chart p : E) ∈ s)
    (hTX : TX ⊆ M.collar) (hTY : TY ⊆ M.collar)
    (hX : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (M.chart p : E) ∈ TX ↔ (p : E × ℝ).1 ∈ (k ∩ s) ∪ {q})
    (hY : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (M.chart p : E) ∈ TY ↔ (p : E × ℝ).1 ∈ b) :
    TX ⊆ s ∧ TY ⊆ s ∧ M.collar ∩ s = TX ∪ TY ∧
      TX ∩ TY ⊆ {q} ∧ d ∩ TX ⊆ {q} ∧
      TX ∩ ((M.residual ∩ s) ∪ (TY ∪ d)) = TX ∩ M.residual := by
  have hTS : M.collar ⊆ S :=
    (subset_union_left.trans M.cover.subset).trans inter_subset_left
  have hbzero : b ⊆ {x | A x = 0} :=
    (subset_union_left.trans hB.symm.subset).trans inter_subset_right
  have hbaseSide := M.chart.collar_fiber_mem_cut_iff M.height M.bottom hs hs'
    (hTS.trans hunion.symm.subset) hinter hbzero
  have hXs : TX ⊆ s := by
    intro x hx
    let p := M.chart.symm ⟨x, hTX hx⟩
    have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
    rcases (hX p).mp (hp.symm ▸ hx) with hpk | hpq
    · by_cases hpb : (p : E × ℝ).1 ∈ b
      · exact hp ▸ hselected p hpb
      · exact hp ▸ (hbaseSide p hpb).1.mpr hpk.2
    · have hxq : x = q := hp.symm.trans (M.chart_eq_apex_of_base_eq p hpq)
      exact hxq.symm ▸ hqs
  have hYs : TY ⊆ s := by
    intro x hx
    let p := M.chart.symm ⟨x, hTY hx⟩
    have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
    exact hp ▸ hselected p ((hY p).mp (hp.symm ▸ hx))
  have hXY : TX ∩ TY ⊆ {q} := by
    intro x hx
    let p := M.chart.symm ⟨x, hTX hx.1⟩
    have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
    have hpb := (hY p).mp (hp.symm ▸ hx.2)
    have hpq : (p : E × ℝ).1 = q := by
      rcases (hX p).mp (hp.symm ▸ hx.1) with hpk | hpq
      · exact htouch ⟨hpb, hpk.1⟩
      · exact hpq
    exact hp.symm.trans (M.chart_eq_apex_of_base_eq p hpq)
  have hdX : d ∩ TX ⊆ {q} := by
    intro x hx
    have hxb : x ∈ b := hcap.subset ⟨hx.1, hTS (hTX hx.2)⟩
    let p := M.chart.symm ⟨x, hTX hx.2⟩
    have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
    have hz : (p : E × ℝ).2 = 0 :=
      (M.height p).symm.trans ((congrArg A hp).trans (hbzero hxb))
    have hpx : (p : E × ℝ).1 = x := (M.bottom p hz).symm.trans hp
    rcases (hX p).mp (hp.symm ▸ hx.2) with hpk | hpq
    · exact htouch ⟨hxb, hpx ▸ hpk.1⟩
    · exact hpx.symm.trans hpq
  refine ⟨hXs, hYs, ?_, hXY, hdX, ?_⟩
  · ext x
    constructor
    · intro hx
      let p := M.chart.symm ⟨x, hx.1⟩
      have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
      by_cases hpb : (p : E × ℝ).1 ∈ b
      · exact Or.inr (hp ▸ (hY p).mpr hpb)
      · have hpk : (p : E × ℝ).1 ∈ k := (hB.subset p.property.1).resolve_left hpb
        have hps : (p : E × ℝ).1 ∈ s := (hbaseSide p hpb).1.mp (hp.symm ▸ hx.2)
        exact Or.inl (hp ▸ (hX p).mpr (Or.inl ⟨hpk, hps⟩))
    · exact fun hx => hx.elim (fun h => ⟨hTX h, hXs h⟩) (fun h => ⟨hTY h, hYs h⟩)
  · ext x
    constructor
    · rintro ⟨hx, hxR | hxT | hxd⟩
      · exact ⟨hx, hxR.1⟩
      · exact ⟨hx, (hXY ⟨hx, hxT⟩ : x = q).symm ▸ M.apex_mem_residual⟩
      · exact ⟨hx, (hdX ⟨hxd, hx⟩ : x = q).symm ▸ M.apex_mem_residual⟩
    · exact fun hx => ⟨hx.1, Or.inl ⟨hx.2, hXs hx.1⟩⟩

end Geometry
