import PoincareConjecture.Proofs.M76.Brown.NormalChartTransitions










set_option autoImplicit false

open Set

namespace BrownCollar

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]



theorem normal_product_transition_pair
    (q r : OpenPartialHomeomorph (P × ℝ) X) (S : Set X)
    (hq : ∀ z ∈ q.source, q z ∈ S ↔ z.2 = 0)
    (hr : ∀ z ∈ r.source, r z ∈ S ↔ z.2 = 0) :
    ∀ z ∈ (q.trans r.symm).source, ((q.trans r.symm) z).2 = 0 ↔ z.2 = 0 := by
  intro z hz
  have hzq : z ∈ q.source := hz.1
  have hzr : q z ∈ r.target := hz.2
  change (r.symm (q z)).2 = 0 ↔ z.2 = 0
  calc
    _ ↔ r (r.symm (q z)) ∈ S := (hr _ (r.map_target hzr)).symm
    _ ↔ q z ∈ S := by rw [r.right_inv hzr]
    _ ↔ z.2 = 0 := hq z hzq




theorem normal_product_transition_base
    (q r : OpenPartialHomeomorph (P × ℝ) X) (x : P)
    (hqx : (x, (0 : ℝ)) ∈ q.source) (hrx : (x, (0 : ℝ)) ∈ r.source)
    (hzero : q (x, 0) = r (x, 0)) :
    (x, (0 : ℝ)) ∈ (q.trans r.symm).source ∧
      (q.trans r.symm) (x, 0) = (x, 0) := by
  constructor
  · refine ⟨hqx, ?_⟩
    change q (x, 0) ∈ r.target
    rw [hzero]
    exact r.map_source hrx
  · change r.symm (q (x, 0)) = (x, 0)
    rw [hzero, r.left_inv hrx]



theorem normal_product_sign_cocycle
    (q r t : OpenPartialHomeomorph (P × ℝ) X) (x : P)
    (hbase : (q.trans r.symm) (x, 0) = (x, 0))
    {s₁ s₂ s₃ : SignType}
    (hqr : NormalSignAt (q.trans r.symm) x s₁)
    (hrt : NormalSignAt (r.trans t.symm) x s₂)
    (hqt : NormalSignAt (q.trans t.symm) x s₃) : s₂ * s₁ = s₃ := by
  have hrt' : NormalSignAt (r.trans t.symm) ((q.trans r.symm) (x, 0)).1 s₂ := by
    rw [hbase]
    exact hrt
  obtain ⟨hsource, heq⟩ := chart_transition_cancellation q.symm r.symm t.symm
  exact ((hqr.trans hrt').of_source_subset hsource heq).unique hqt

end BrownCollar
