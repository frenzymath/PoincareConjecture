import PoincareConjecture.Proofs.M76.Brown.OrientedFlatteningCharts

set_option autoImplicit false

open Set SignType

namespace BrownCollar

variable {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]

theorem NormalSignAt.exists_open_product_agreement
    {q r : OpenPartialHomeomorph (P × ℝ) X} {x : P} {ci ck : SignTypeˣ}
    (h : NormalSignAt (q.trans r.symm) x ((ck : SignType) * (ci : SignType)))
    (ni nk : X → ℝ)
    (hni : ∀ w ∈ q.source, ni (q w) = w.2)
    (hnk : ∀ w ∈ r.source, nk (r w) = w.2) :
    ∃ V : Set X, IsOpen V ∧ q (x, 0) ∈ V ∧ V ⊆ q.target ∩ r.target ∧
      EqOn (fun y => sign (normalScalar ci * ni y))
        (fun y => sign (normalScalar ck * nk y)) V := by
  obtain ⟨_, U, hU, hxU, hUs, hsign⟩ := h
  have hUq : U ⊆ q.source := fun w hw => (hUs hw).1
  refine ⟨q '' U, q.isOpen_image_of_subset_source hU hUq,
    mem_image_of_mem q hxU, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    have hwr : q w ∈ r.target := (hUs hw).2
    exact ⟨q.map_source (hUq hw), hwr⟩
  · rintro _ ⟨w, hw, rfl⟩
    have hwr : q w ∈ r.target := (hUs hw).2
    have hnk' : nk (q w) = (r.symm (q w)).2 := by
      have hn := hnk (r.symm (q w)) (r.map_target hwr)
      rwa [r.right_inv hwr] at hn
    have hs := hsign w hw
    change sign (r.symm (q w)).2 =
      ((ck : SignType) * (ci : SignType)) * sign w.2 at hs
    change sign (normalScalar ci * ni (q w)) = sign (normalScalar ck * nk (q w))
    rw [normalScalar_sign, normalScalar_sign, hni w (hUq hw), hnk', hs]
    have hsq : (ck : SignType) * (ck : SignType) = 1 := mul_inv_cancel₀ ck.ne_zero
    calc
      (ci : SignType) * sign w.2 =
          ((ck : SignType) * (ck : SignType)) * ((ci : SignType) * sign w.2) := by
            rw [hsq, one_mul]
      _ = (ck : SignType) * (((ck : SignType) * (ci : SignType)) * sign w.2) := by
        ac_rfl

end BrownCollar
