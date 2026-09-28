import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

open Function unitInterval

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X} (hp : IsCoveringMap p)

noncomputable def identityHomotopyLift {f : C(X, X)}
    (H : (ContinuousMap.id X).Homotopy f) : C(I × E, E) :=
  hp.liftHomotopy
    ⟨fun te => H (te.1, p te.2),
      H.continuous.comp (continuous_fst.prodMk (hp.continuous.comp continuous_snd))⟩
    (ContinuousMap.id E) (fun e => H.apply_zero (p e))

theorem identityHomotopyLift_lifts {f : C(X, X)}
    (H : (ContinuousMap.id X).Homotopy f) (t : I) (e : E) :
    p (hp.identityHomotopyLift H (t, e)) = H (t, p e) :=
  congrFun (hp.liftHomotopy_lifts _ _ _) (t, e)

theorem identityHomotopyLift_zero {f : C(X, X)}
    (H : (ContinuousMap.id X).Homotopy f) (e : E) :
    hp.identityHomotopyLift H (0, e) = e :=
  hp.liftHomotopy_zero _ _ _ e

theorem identityHomotopyLift_reverse
    {g : X ≃ₜ X} (H : (ContinuousMap.id X).Homotopy ⟨g, g.continuous⟩)
    (R : (ContinuousMap.id X).Homotopy ⟨g.symm, g.symm.continuous⟩)
    (hR : ∀ t x, R (t, x) = H (σ t, g.symm x)) (e : E) :
    hp.identityHomotopyLift R (1, hp.identityHomotopyLift H (1, e)) = e := by
  let L := hp.identityHomotopyLift H
  let K := hp.identityHomotopyLift R
  have he : p (L (1, e)) = g (p e) :=
    (hp.identityHomotopyLift_lifts H 1 e).trans (H.apply_one _)
  have hpaths : (fun t : I => K (t, L (1, e))) = fun t => L (σ t, e) := by
    refine hp.eq_of_comp_eq
      (K.continuous.comp (continuous_id.prodMk continuous_const))
      (L.continuous.comp (continuous_symm.prodMk continuous_const)) ?_ 0 ?_
    · funext t
      change p (K (t, L (1, e))) = p (L (σ t, e))
      rw [hp.identityHomotopyLift_lifts R, hp.identityHomotopyLift_lifts H (σ t) e,
        hR, he, g.symm_apply_apply]
    · rw [hp.identityHomotopyLift_zero R, symm_zero]
  have h := congrFun hpaths 1
  simpa only [symm_one, identityHomotopyLift_zero, L, K] using h

theorem exists_homeomorph_lift_of_homotopy
    (g : X ≃ₜ X) (H : (ContinuousMap.id X).Homotopy ⟨g, g.continuous⟩) :
    ∃ G : E ≃ₜ E, ∀ e, G e = hp.identityHomotopyLift H (1, e) := by
  let R : (ContinuousMap.id X).Homotopy ⟨g.symm, g.symm.continuous⟩ :=
    { toFun tx := H (σ tx.1, g.symm tx.2)
      continuous_toFun := H.continuous.comp
        ((continuous_symm.comp continuous_fst).prodMk
          (g.symm.continuous.comp continuous_snd))
      map_zero_left := fun x => by
        rw [symm_zero, H.apply_one]
        exact g.apply_symm_apply x
      map_one_left := fun x => by
        change H (σ 1, g.symm x) = g.symm x
        rw [symm_one]
        exact H.apply_zero (g.symm x) }
  let L := hp.identityHomotopyLift H
  let K := hp.identityHomotopyLift R
  refine ⟨{ toFun := fun e => L (1, e)
            invFun := fun e => K (1, e)
            left_inv := hp.identityHomotopyLift_reverse H R (fun _ _ => rfl)
            right_inv := ?_
            continuous_toFun := L.continuous.comp (continuous_const.prodMk continuous_id)
            continuous_invFun := K.continuous.comp (continuous_const.prodMk continuous_id) },
    fun _ => rfl⟩
  apply hp.identityHomotopyLift_reverse R H
  intro t x
  change H (t, x) = H (σ (σ t), g.symm (g x))
  rw [symm_symm, g.symm_apply_apply]

end IsCoveringMap
