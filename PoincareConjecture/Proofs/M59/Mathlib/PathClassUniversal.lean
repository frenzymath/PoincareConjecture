import PoincareConjecture.Proofs.M59.Mathlib.PathClassLifts

set_option autoImplicit false

open Set
open scoped unitInterval

universe u

namespace PathClassCover

variable {X : Type u} [TopologicalSpace X] [LocallySimplyConnectedSpace X] {x₀ : X}

theorem loop_nullhomotopic [PathConnectedSpace X] (a : PathClassCover x₀) (r : Path a a) :
    r.Homotopic (Path.refl a) := by
  rcases a with ⟨x, alpha⟩
  let a : PathClassCover x₀ := ⟨x, alpha⟩
  let p : Path x x := r.map (continuous_endpoint x₀)
  let g : I → PathClassCover x₀ := fun t => append a (pathFromBase p t)
  have hg : Continuous g := (continuous_append a).comp (pathFromBase p).continuous
  have hproj : endpoint ∘ r = endpoint ∘ g := by
    funext t
    change (r t).endpoint = (pathFromBase p t).endpoint
    rw [endpoint_pathFromBase]
    rfl
  have hzero : r 0 = g 0 := by
    change r 0 = append a (pathFromBase p 0)
    rw [(pathFromBase p).source, append_basepoint, r.source]
  have he := congrFun ((isCoveringMap_endpoint x₀).eq_of_comp_eq
    r.continuous hg hproj 0 hzero) 1
  change r 1 = append a (pathFromBase p 1) at he
  rw [r.target, Path.target] at he
  have hc : alpha = alpha.trans (.mk p) := eq_of_heq (PathClassCover.mk.inj he).2
  have hp : Path.Homotopic.Quotient.mk p = .refl x := by
    have hh := congrArg (Path.Homotopic.Quotient.trans alpha.symm) hc
    rw [← Path.Homotopic.Quotient.trans_assoc] at hh
    simpa using hh.symm
  apply Path.Homotopic.Quotient.eq.mp
  apply (isCoveringMap_endpoint x₀).injective_path_homotopic_map _ _
  exact hp

instance simplyConnectedSpace [PathConnectedSpace X] (x₀ : X) :
    SimplyConnectedSpace (PathClassCover x₀) :=
  simply_connected_iff_loops_nullhomotopic.mpr
    ⟨inferInstance, fun a r => loop_nullhomotopic a r⟩

noncomputable def deck (q : Path.Homotopic.Quotient x₀ x₀) :
    PathClassCover x₀ ≃ₜ PathClassCover x₀ where
  toFun := append ⟨x₀, q⟩
  invFun := append ⟨x₀, q.symm⟩
  left_inv a := by
    refine ext ?_ ?_
    · rfl
    change HEq (q.symm.trans (q.trans a.pathClass)) a.pathClass
    exact heq_of_eq (by rw [← Path.Homotopic.Quotient.trans_assoc]; simp)
  right_inv a := by
    refine ext ?_ ?_
    · rfl
    change HEq (q.trans (q.symm.trans a.pathClass)) a.pathClass
    exact heq_of_eq (by rw [← Path.Homotopic.Quotient.trans_assoc]; simp)
  continuous_toFun := continuous_append _
  continuous_invFun := continuous_append _

@[simp] theorem endpoint_deck (q : Path.Homotopic.Quotient x₀ x₀)
    (a : PathClassCover x₀) : (deck q a).endpoint = a.endpoint := rfl

theorem exists_deck_apply_eq (a b : PathClassCover x₀) (h : a.endpoint = b.endpoint) :
    ∃ q : Path.Homotopic.Quotient x₀ x₀, deck q a = b := by
  rcases a with ⟨x, alpha⟩
  rcases b with ⟨y, beta⟩
  change x = y at h
  subst y
  refine ⟨beta.trans alpha.symm, ext rfl ?_⟩
  change HEq ((beta.trans alpha.symm).trans alpha) beta
  exact heq_of_eq (by simp)

end PathClassCover
