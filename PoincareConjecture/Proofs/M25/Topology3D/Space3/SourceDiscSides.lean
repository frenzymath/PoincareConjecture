import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarComplementSides
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceDiscBoundary












set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M25.Topology3D



theorem sourceDisc_boundary_image (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (q : UnitCircle → UnitTwoSphere) (hq : ∀ θ : UnitCircle, e θ.1 = q θ) :
    e '' sphere 0 1 = range q := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, (hq ⟨x, hx⟩).symm⟩
  · rintro ⟨θ, rfl⟩
    exact ⟨θ.1, θ.2, hq θ⟩



theorem source_disc_collar_halves
    (Q : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere)
    {d : ℝ} (hd : 0 < d) (hs : Q.source = univ ×ˢ Ioo (-d) d)
    (e f : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : closedBall 0 1 ⊆ e.source) (hf : closedBall 0 1 ⊆ f.source)
    (q : UnitCircle → UnitTwoSphere) (hQ : ∀ θ, Q (θ, 0) = q θ)
    (heq : ∀ θ : UnitCircle, e θ.1 = q θ) (hfq : ∀ θ : UnitCircle, f θ.1 = q θ)
    (hdis : Disjoint (e '' ball 0 1) (f '' ball 0 1))
    (hcover : (e '' ball 0 1) ∪ (f '' ball 0 1) = (range q)ᶜ) :
    (Q '' (univ ×ˢ Ioo (-d) 0) ⊆ e '' ball 0 1 ∧
      Q '' (univ ×ˢ Ioo 0 d) ⊆ f '' ball 0 1) ∨
    (Q '' (univ ×ˢ Ioo (-d) 0) ⊆ f '' ball 0 1 ∧
      Q '' (univ ×ˢ Ioo 0 d) ⊆ e '' ball 0 1) := by
  have hdim : 1 < Module.rank ℝ E2 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E2])
  let : PreconnectedSpace UnitCircle :=
    Subtype.preconnectedSpace (isPreconnected_sphere hdim (0 : E2) 1)
  have : Nonempty UnitCircle :=
    (NormedSpace.sphere_nonempty (E := E2) (x := 0) |>.mpr zero_le_one).coe_sort
  have heb := sourceDisc_boundary_image e q heq
  have hfb := sourceDisc_boundary_image f q hfq
  have hcentral : Q '' (univ ×ˢ {0}) = range q := by
    ext p
    constructor
    · rintro ⟨⟨θ, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨θ, (hQ θ).symm⟩
    · rintro ⟨θ, rfl⟩
      exact ⟨(θ, 0), ⟨mem_univ _, rfl⟩, hQ θ⟩
  apply collar_complement_halves Q hd hs
    (e.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans he))
    (f.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hf))
    hdis hcover hcentral
  intro p hp
  rw [compactChart_closure_ball e 0 zero_lt_one he,
    compactChart_closure_ball f 0 zero_lt_one hf]
  exact ⟨image_mono sphere_subset_closedBall (heb.symm ▸ hp),
    image_mono sphere_subset_closedBall (hfb.symm ▸ hp)⟩

end PoincareConjecture.M25.Topology3D
