import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.Collar

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.UpperAnnularEnd

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {v : E3} {g : S2 → E3} {B : Set Real}
  {D : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}

def cappedRegion (A : UpperAnnularEnd D C h a b) (c : Real) : Set S2 :=
  (D.chart '' closedBall 0 1) ∪ A.chart '' (univ ×ˢ Icc c D.center)

theorem cappedRegion_eq_reflected (A : UpperAnnularEnd D C h a b) (c : Real) :
    A.cappedRegion c = A.reflected.cappedRegion (-c) := by
  unfold cappedRegion LowerAnnularEnd.cappedRegion
  rw [A.image_closed_strip]
  rfl

theorem exists_cappedRegion_disk (A : UpperAnnularEnd D C h a b)
    (hDb : D.center ≤ b) {c : Real} (hac : a < c) (hcD : c < D.center) :
    ∃ d : OpenPartialHomeomorph E2 S2,
      closedBall 0 1 ⊆ d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target ∧
      d '' closedBall 0 1 = A.cappedRegion c := by
  obtain ⟨d, hds, hd, hdi, hdc, _⟩ := A.reflected.exists_cappedRegion_disk
    (neg_le_neg hDb) (neg_lt_neg hcD) (neg_lt_neg hac)
  exact ⟨d, hds, hd, hdi, hdc.trans (A.cappedRegion_eq_reflected c).symm⟩

theorem exists_physical_terminal_collar_in (A : UpperAnnularEnd D C h a b)
    (hg : Continuous g) (hDb : D.center ≤ b)
    {c : Real} (hac : a < c) (hcD : c < D.center)
    {U : Set E3} (hU : IsOpen U) (hEU : g '' A.cappedRegion c ⊆ U) :
    ∃ ε : Real, 0 < ε ∧ Icc (c - ε) (c + ε) ⊆ Ioo a D.center ∧
      A.chart '' (univ ×ˢ Icc (c - ε) (c + ε)) ⊆ _root_.interior C ∧
      g '' (A.chart '' (univ ×ˢ Icc (c - ε) (c + ε))) ⊆ U ∧
      ∀ q t, t ∈ Icc (c - ε) (c + ε) →
        inner Real v (g (A.chart (q, t))) = t := by
  obtain ⟨δ, hδ, hδsub⟩ := Saddle.Caps.exists_terminal_collar_in A.chart hg (by
    intro q
    rw [A.source]
    exact ⟨mem_univ _, by linarith [A.reflected.delta_pos],
      by linarith [A.reflected.delta_pos]⟩) hU (by
    intro q
    apply hEU
    exact mem_image_of_mem g (Or.inr (mem_image_of_mem A.chart
      ⟨mem_univ _, le_rfl, hcD.le⟩)))
  let ε := min δ (min (c - a) (D.center - c) / 2)
  have hε : 0 < ε := lt_min hδ (half_pos (lt_min (sub_pos.mpr hac) (sub_pos.mpr hcD)))
  have hsmall : Icc (c - ε) (c + ε) ⊆ Icc (c - δ) (c + δ) := by
    intro t ht
    have he := min_le_left δ (min (c - a) (D.center - c) / 2)
    constructor <;> dsimp [ε] at ht <;> linarith [ht.1, ht.2]
  have hi : Icc (c - ε) (c + ε) ⊆ Ioo a D.center := by
    intro t ht
    have he := min_le_right δ (min (c - a) (D.center - c) / 2)
    have hl := min_le_left (c - a) (D.center - c)
    have hr := min_le_right (c - a) (D.center - c)
    constructor <;> dsimp [ε] at ht <;> linarith [ht.1, ht.2]
  exact ⟨ε, hε, hi, (image_mono (prod_mono Subset.rfl hi)).trans A.interior,
    (image_mono (image_mono (prod_mono Subset.rfl hsmall))).trans hδsub,
    fun q t ht => A.actual_height q t ⟨(hi ht).1.le, (hi ht).2.le⟩⟩

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.UpperAnnularEnd
