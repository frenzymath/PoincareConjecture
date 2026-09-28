import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallLocalInterior

set_option autoImplicit false

open Set

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {d b R : Set X}

theorem IsFinitePLBallPair.boundary_height_side (hd : IsFinitePLBallPair E d b)
    (f : X → ℝ) (hf : ContinuousOn f d) (hbzero : ∀ x ∈ b, f x = 0)
    (q : X) (hbconn : IsPreconnected (b \ {q})) (hR : IsClosed R)
    (hbR : b ∩ R ⊆ {q}) (hzeros : (d ∩ {x | f x = 0}) \ b ⊆ R) :
    b ∩ closure (d ∩ {x | f x < 0}) ⊆ {q} ∨
      b ∩ closure (d ∩ {x | 0 < f x}) ⊆ {q} := by
  let P := (closure (d ∩ {x | f x < 0}))ᶜ
  let N := (closure (d ∩ {x | 0 < f x}))ᶜ
  have hlocal (x : X) (hx : x ∈ b \ {q}) :
      (x ∈ P ∧ x ∈ closure (d ∩ {y | 0 < f y})) ∨
        (x ∈ N ∧ x ∈ closure (d ∩ {y | f y < 0})) := by
    have hxR : x ∉ R := fun hr => hx.2 (hbR ⟨hx.1, hr⟩)
    obtain ⟨V, hV, hxV, hVR, hconn⟩ :=
      hd.exists_preconnected_sdiff_neighborhood (hd.1 hx.1) hR.isOpen_compl hxR
    have hnonzero : ∀ y ∈ (d \ b) ∩ V, f y ≠ 0 := by
      rintro y ⟨hy, hyV⟩ hy0
      exact hVR hyV (hzeros ⟨⟨hy.1, hy0⟩, hy.2⟩)
    have hxc : x ∈ closure ((d \ b) ∩ V) := by
      apply mem_closure_iff.mpr
      intro U hU hxU
      have hxd : x ∈ closure (d \ b) := hd.closure_sdiff.symm ▸ hd.1 hx.1
      obtain ⟨y, hyUV, hyd⟩ := mem_closure_iff.mp hxd (U ∩ V) (hU.inter hV) ⟨hxU, hxV⟩
      exact ⟨y, hyUV.1, hyd, hyUV.2⟩
    rcases hconn.mapsTo_Ioi_or_Iio (hf.mono (inter_subset_left.trans sdiff_subset))
        hnonzero with hpos | hneg
    · have hdis : Disjoint V (d ∩ {y | f y < 0}) := by
        apply Set.disjoint_left.mpr
        rintro y hyV ⟨hyd, hyneg⟩
        by_cases hyb : y ∈ b
        · have hz := hbzero y hyb
          exact (not_lt_of_ge (le_of_eq hz.symm)) hyneg
        · have hpy : 0 < f y := hpos ⟨⟨hyd, hyb⟩, hyV⟩
          exact (not_lt_of_ge hpy.le) hyneg
      exact Or.inl ⟨fun hcl => Set.disjoint_left.mp (hdis.closure_right hV) hxV hcl,
        closure_mono (show (d \ b) ∩ V ⊆ d ∩ {y | 0 < f y} from
          fun y hy => ⟨hy.1.1, hpos hy⟩) hxc⟩
    · have hdis : Disjoint V (d ∩ {y | 0 < f y}) := by
        apply Set.disjoint_left.mpr
        rintro y hyV ⟨hyd, hypos⟩
        by_cases hyb : y ∈ b
        · have hz := hbzero y hyb
          exact (not_lt_of_ge (le_of_eq hz)) hypos
        · have hny : f y < 0 := hneg ⟨⟨hyd, hyb⟩, hyV⟩
          exact (not_lt_of_ge hny.le) hypos
      exact Or.inr ⟨fun hcl => Set.disjoint_left.mp (hdis.closure_right hV) hxV hcl,
        closure_mono (show (d \ b) ∩ V ⊆ d ∩ {y | f y < 0} from
          fun y hy => ⟨hy.1.1, hneg hy⟩) hxc⟩
  have hcover : b \ {q} ⊆ P ∪ N := fun x hx =>
    (hlocal x hx).imp And.left And.left
  have hchoice : b \ {q} ⊆ P ∨ b \ {q} ⊆ N := by
    by_cases hp : b \ {q} ⊆ P
    · exact Or.inl hp
    right
    intro y hy
    by_contra hyN
    obtain ⟨x, hx, hxP⟩ := Set.not_subset.mp hp
    have hxN := (hcover hx).resolve_left hxP
    have hyP := (hcover hy).resolve_right hyN
    obtain ⟨z, hz, hzP, hzN⟩ := hbconn P N isClosed_closure.isOpen_compl
      isClosed_closure.isOpen_compl hcover ⟨y, hy, hyP⟩ ⟨x, hx, hxN⟩
    rcases hlocal z hz with hpos | hneg
    · exact hzN hpos.2
    · exact hzP hneg.2
  rcases hchoice with hp | hn
  · left
    rintro x ⟨hxb, hxc⟩
    by_contra hxq
    exact hp ⟨hxb, hxq⟩ hxc
  · right
    rintro x ⟨hxb, hxc⟩
    by_contra hxq
    exact hn ⟨hxb, hxq⟩ hxc

end Set
