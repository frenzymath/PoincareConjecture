import PoincareConjecture.Proofs.M76.Brown.NormalSignGerms









set_option autoImplicit false

open Set

namespace BrownCollar

variable {X P Q R : Type*} [TopologicalSpace X] [TopologicalSpace P]
  [TopologicalSpace Q] [TopologicalSpace R]



theorem NormalSignAt.of_source_subset
    {e f : OpenPartialHomeomorph (P × ℝ) (Q × ℝ)} {p : P} {s : SignType}
    (h : NormalSignAt e p s) (hsource : e.source ⊆ f.source)
    (heq : EqOn e f e.source) : NormalSignAt f p s := by
  obtain ⟨hs, U, hU, hp, hUs, hsign⟩ := h
  refine ⟨hs, U, hU, hp, hUs.trans hsource, ?_⟩
  intro z hz
  rw [← heq (hUs hz)]
  exact hsign z hz




theorem chart_transition_cancellation
    (e : OpenPartialHomeomorph X (P × ℝ))
    (f : OpenPartialHomeomorph X (Q × ℝ))
    (g : OpenPartialHomeomorph X (R × ℝ)) :
    ((e.symm.trans f).trans (f.symm.trans g)).source ⊆ (e.symm.trans g).source ∧
      EqOn ((e.symm.trans f).trans (f.symm.trans g)) (e.symm.trans g)
        ((e.symm.trans f).trans (f.symm.trans g)).source := by
  constructor
  · intro z hz
    refine ⟨hz.1.1, ?_⟩
    have hfs : e.symm z ∈ f.source := hz.1.2
    have hfg := hz.2.2
    change f.symm (f (e.symm z)) ∈ g.source at hfg
    rw [f.left_inv hfs] at hfg
    exact hfg
  · intro z hz
    have hfs : e.symm z ∈ f.source := hz.1.2
    change g (f.symm (f (e.symm z))) = g (e.symm z)
    rw [f.left_inv hfs]



theorem normal_chart_sign_cocycle
    (e : OpenPartialHomeomorph X (P × ℝ))
    (f : OpenPartialHomeomorph X (Q × ℝ))
    (g : OpenPartialHomeomorph X (R × ℝ))
    (x : X) (hx : x ∈ e.source) (he0 : (e x).2 = 0)
    {s t u : SignType}
    (hef : NormalSignAt (e.symm.trans f) (e x).1 s)
    (hfg : NormalSignAt (f.symm.trans g) (f x).1 t)
    (heg : NormalSignAt (e.symm.trans g) (e x).1 u) : t * s = u := by
  have hbase : ((e x).1, (0 : ℝ)) = e x := by
    apply Prod.ext
    · rfl
    · exact he0.symm
  have hfg' : NormalSignAt (f.symm.trans g)
      ((e.symm.trans f) ((e x).1, 0)).1 t := by
    change NormalSignAt (f.symm.trans g) (f (e.symm ((e x).1, 0))).1 t
    rw [hbase, e.left_inv hx]
    exact hfg
  obtain ⟨hsource, heq⟩ := chart_transition_cancellation e f g
  exact ((hef.trans hfg').of_source_subset hsource heq).unique heg

end BrownCollar
