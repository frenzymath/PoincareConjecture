import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveSelectedIncidence

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem AlexanderCollarSlab.ordinary_collar_decomposition
    {S s s' b k d TX TY : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs : IsClosed s) (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hinter : s ∩ s' ⊆ b) (hB : S ∩ {x | A x = 0} = b ∪ k)
    (htouch : Disjoint b k) (hcap : d ∩ S = b)
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ b → (M.chart p : E) ∈ s)
    (hTX : TX ⊆ M.collar) (hTY : TY ⊆ M.collar)
    (hX : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (M.chart p : E) ∈ TX ↔ (p : E × ℝ).1 ∈ k ∩ s)
    (hY : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (M.chart p : E) ∈ TY ↔ (p : E × ℝ).1 ∈ b) :
    TX ⊆ s ∧ TY ⊆ s ∧ M.collar ∩ s = TX ∪ TY ∧
      Disjoint TX TY ∧ Disjoint d TX := by
  have hTS : M.collar ⊆ S :=
    (subset_union_left.trans M.cover.subset).trans inter_subset_left
  have hbzero : b ⊆ {x | A x = 0} :=
    (subset_union_left.trans hB.symm.subset).trans inter_subset_right
  have hfiber := M.chart.collar_fiber_mem_cut_iff M.height M.bottom hs hs'
    (hTS.trans hunion.symm.subset) hinter hbzero
  have hXs : TX ⊆ s := by
    intro x hx
    let p := M.chart.symm ⟨x, hTX hx⟩
    have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
    have hpk := (hX p).mp (hp.symm ▸ hx)
    have hpb : (p : E × ℝ).1 ∉ b :=
      fun hb => disjoint_left.mp htouch hb hpk.1
    exact hp ▸ (hfiber p hpb).1.mpr hpk.2
  have hYs : TY ⊆ s := by
    intro x hx
    let p := M.chart.symm ⟨x, hTY hx⟩
    have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
    exact hp ▸ hselected p ((hY p).mp (hp.symm ▸ hx))
  refine ⟨hXs, hYs, ?_, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      let p := M.chart.symm ⟨x, hx.1⟩
      have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
      by_cases hpb : (p : E × ℝ).1 ∈ b
      · exact Or.inr (hp ▸ (hY p).mpr hpb)
      · have hpk := (hB.subset p.property.1).resolve_left hpb
        have hps := (hfiber p hpb).1.mp (hp.symm ▸ hx.2)
        exact Or.inl (hp ▸ (hX p).mpr ⟨hpk, hps⟩)
    · exact fun hx => hx.elim (fun h => ⟨hTX h, hXs h⟩) (fun h => ⟨hTY h, hYs h⟩)
  · apply disjoint_left.mpr
    intro x hx hy
    let p := M.chart.symm ⟨x, hTX hx⟩
    have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
    exact disjoint_left.mp htouch ((hY p).mp (hp.symm ▸ hy))
      ((hX p).mp (hp.symm ▸ hx)).1
  · apply disjoint_left.mpr
    intro x hxd hx
    have hxb : x ∈ b := hcap.subset ⟨hxd, hTS (hTX hx)⟩
    let p := M.chart.symm ⟨x, hTX hx⟩
    have hp : (M.chart p : E) = x := congrArg Subtype.val (M.chart.apply_symm_apply _)
    have hz : (p : E × ℝ).2 = 0 :=
      (M.height p).symm.trans ((congrArg A hp).trans (hbzero hxb))
    have hpx : (p : E × ℝ).1 = x := (M.bottom p hz).symm.trans hp
    exact disjoint_left.mp htouch (hpx.symm ▸ hxb) ((hX p).mp (hp.symm ▸ hx)).1

end Geometry
