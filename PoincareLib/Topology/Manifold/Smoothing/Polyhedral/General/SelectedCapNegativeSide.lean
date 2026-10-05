import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Collars.CollarBottomClosure
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.PlanarCapHeightSide

/-!
# Negative-side avoidance for the positive collar's cut disk

The collar bottom limit excludes the positive-closure alternative
in the planar cap's boundary-side dichotomy. See Alexander 1924,
pp. 7--8 and M76 derivation 238.
-/

set_option autoImplicit false

open Set

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A planar cap avoids the selected disk's negative-height
closure except at the marked point when that disk contains
the rim's positive collar. See Alexander pp. 7--8 and
derivation 238. -/
theorem IsFinitePLBallPair.cap_negative_side_of_positive_collar
    {s b d R B T : Set X} (hs : IsFinitePLBallPair E s b)
    {upper A : X → ℝ}
    (C : {p : X × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T)
    (hheight : ∀ p, A (C p) = (p : X × ℝ).2)
    (hbottom : ∀ p : {p : X × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : X × ℝ).2 = 0 → (C p : X) = (p : X × ℝ).1)
    (hbB : b ⊆ B) (hbd : b ⊆ d) (hA : ContinuousOn A s)
    (hdplane : d ⊆ {x | A x = 0}) (hdmeet : d ∩ s ⊆ b)
    (q : X) (hbconn : IsConnected (b \ {q}))
    (hR : IsClosed R) (hbR : b ∩ R ⊆ {q})
    (hzeros : (s ∩ {x | A x = 0}) \ b ⊆ R)
    (hpos : ∀ x ∈ b, x ≠ q → 0 < upper x)
    (hselected : ∀ p : {p : X × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : X × ℝ).1 ∈ b → (C p : X) ∈ s) :
    d ∩ closure ((s ∪ d) ∩ {x | A x < 0}) ⊆ {q} := by
  rcases hs.cap_height_side A hA (fun x hx => hdplane (hbd hx))
      (fun x hx => hdplane hx) hdmeet q hbconn.isPreconnected hR hbR hzeros with hn | hp
  · exact hn
  · obtain ⟨x, hxb, hxq⟩ := hbconn.nonempty
    have hcl : x ∈ closure (s ∩ {y | 0 < A y}) :=
      C.collar_bottom_mem_closure_positive hheight hbottom (hbB hxb) (hpos x hxb hxq)
        (fun p heq _ => hselected p (heq.symm ▸ hxb))
    have hcl' : x ∈ closure ((s ∪ d) ∩ {y | 0 < A y}) :=
      closure_mono (inter_subset_inter_left _ subset_union_left) hcl
    exact (hxq (hp ⟨hbd hxb, hcl'⟩)).elim

end Set
