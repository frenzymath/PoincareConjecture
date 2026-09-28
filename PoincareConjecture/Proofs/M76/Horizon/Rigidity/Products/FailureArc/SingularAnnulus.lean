import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.BoundaryLoopPowers

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

private noncomputable def connectorTail {X : Type*} [TopologicalSpace X]
    {x y : X} (k : Path x y) (t : unitInterval) : Path (k t) y :=
  (k.truncate (t : ℝ) 1).cast (by simp [min_eq_left t.property.2]) (by simp)

private theorem connectorTail_continuous {X : Type*} [TopologicalSpace X]
    {x y : X} (k : Path x y) :
    Continuous (fun z : unitInterval × unitInterval => connectorTail k z.1 z.2) := by
  exact k.truncate_continuous_family.comp
    (show Continuous (fun z : unitInterval × unitInterval => ((z.1 : ℝ), (1 : ℝ), z.2)) by
      fun_prop)

private theorem connectorTail_zero {X : Type*} [TopologicalSpace X]
    {x y : X} (k : Path x y) :
    connectorTail k 0 = k.cast k.source rfl := by
  ext s
  simp [connectorTail, Path.truncate_zero_one]

private theorem connectorTail_one {X : Type*} [TopologicalSpace X]
    {x y : X} (k : Path x y) :
    connectorTail k 1 = (Path.refl y).cast k.target rfl := by
  ext s
  simp [connectorTail]

theorem exists_closed_curve_homotopy_of_conjugate
    {X : Type*} [TopologicalSpace X] {x y : X}
    (alpha : Path x x) (beta : Path y y) (k : Path x y)
    (h : alpha.Homotopic (k.trans (beta.trans k.symm))) :
    Nonempty (ContinuousMap.HomotopyWith alpha.toContinuousMap beta.toContinuousMap
      (fun f => f 0 = f 1)) := by
  obtain ⟨H⟩ := h
  let H₀ : ContinuousMap.HomotopyWith alpha.toContinuousMap
      (k.trans (beta.trans k.symm)).toContinuousMap (fun f => f 0 = f 1) :=
    { H.toHomotopy with prop' := fun t => (H.source t).trans (H.target t).symm }
  let loops (t : unitInterval) : Path (k t) (k t) :=
    (connectorTail k t).trans (beta.trans (connectorTail k t).symm)
  have hc : Continuous (fun z : unitInterval × unitInterval => loops z.1 z.2) := by
    exact Path.trans_continuous_family (connectorTail k) (connectorTail_continuous k)
      (fun t => beta.trans (connectorTail k t).symm)
      (Path.trans_continuous_family (fun _ => beta) (beta.continuous.comp continuous_snd)
        (fun t => (connectorTail k t).symm)
        (Path.symm_continuous_family _ (connectorTail_continuous k)))
  let H₁ : ContinuousMap.HomotopyWith
      (k.trans (beta.trans k.symm)).toContinuousMap
      ((Path.refl y).trans (beta.trans (Path.refl y))).toContinuousMap
      (fun f => f 0 = f 1) :=
    { toFun := fun z => loops z.1 z.2
      continuous_toFun := hc
      map_zero_left := by
        intro s
        simp [loops, connectorTail_zero, Path.trans_apply, Path.symm_apply]
      map_one_left := by
        intro s
        simp [loops, connectorTail_one, Path.trans_apply, Path.symm_apply]
      prop' := fun t => (loops t).source.trans (loops t).target.symm }
  obtain ⟨J⟩ := (Path.Homotopic.refl_trans (beta.trans (Path.refl y))).trans
    (Path.Homotopic.trans_refl beta)
  let H₂ : ContinuousMap.HomotopyWith
      ((Path.refl y).trans (beta.trans (Path.refl y))).toContinuousMap
      beta.toContinuousMap (fun f => f 0 = f 1) :=
    { J.toHomotopy with prop' := fun t => (J.source t).trans (J.target t).symm }
  exact ⟨(H₀.trans H₁).trans H₂⟩

theorem exists_circle_cylinder_of_closed_curves
    {X : Type*} [TopologicalSpace X]
    (H : C(unitInterval × unitInterval, X)) (hclosed : ∀ t, H (t, 0) = H (t, 1)) :
    ∃ F : C(unitInterval × AddCircle (1 : ℝ), X),
      ∀ t s : unitInterval, F (t, ((s : ℝ) : AddCircle (1 : ℝ))) = H (t, s) := by
  let q := AddCircle.homeoIccQuot (1 : ℝ) 0
  let flip : C(unitInterval × unitInterval, X) := H.comp ⟨Prod.swap, continuous_swap⟩
  let g : Set.Icc (0 : ℝ) (0 + 1) → C(unitInterval, X) :=
    fun s => flip.curry ⟨s, by simpa using s.property⟩
  have hg : Continuous g := flip.curry.continuous.comp
    (continuous_subtype_val.subtype_mk _)
  have hrel : ∀ a b, AddCircle.EndpointIdent (1 : ℝ) 0 a b → g a = g b := by
    intro a b hab
    cases hab
    apply ContinuousMap.ext
    intro t
    simpa [g, flip] using hclosed t
  let lifted : C(AddCircle (1 : ℝ), C(unitInterval, X)) :=
    ⟨(Quot.lift g hrel) ∘ q, (continuous_quot_lift hrel hg).comp q.continuous⟩
  let F : C(unitInterval × AddCircle (1 : ℝ), X) :=
    lifted.uncurry.comp ⟨Prod.swap, continuous_swap⟩
  refine ⟨F, ?_⟩
  intro t s
  have hq : q (((s : ℝ) : AddCircle (1 : ℝ))) =
      Quot.mk _ (⟨(s : ℝ), by simpa only [zero_add] using s.property⟩ : Set.Icc (0 : ℝ) (0 + 1)) := by
    apply q.symm.injective
    rw [q.symm_apply_apply]
    rfl
  change (Quot.lift g hrel (q (((s : ℝ) : AddCircle (1 : ℝ))))) t = H (t, s)
  rw [hq]
  rfl

theorem exists_singular_boundary_annulus_of_commensurable
    {E₀ E₁ X : Type*}
    [TopologicalSpace E₀] [TopologicalSpace E₁] [TopologicalSpace X]
    (i₀ : C(E₀, X)) (i₁ : C(E₁, X)) (e₀ : E₀) (e₁ : E₁)
    (k : Path (i₀ e₀) (i₁ e₁))
    (hc : (FundamentalGroup.map i₀ e₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom).comp
        (FundamentalGroup.map i₁ e₁)).range)
    (alpha : Path e₀ e₀) :
    ∃ n : ℕ, 0 < n ∧ ∃ (beta : Path e₁ e₁)
      (F : C(unitInterval × AddCircle (1 : ℝ), X)),
      (∀ s : unitInterval,
        F (0, ((s : ℝ) : AddCircle (1 : ℝ))) = i₀ (boundaryLoopIterate alpha n s)) ∧
      (∀ s : unitInterval,
        F (1, ((s : ℝ) : AddCircle (1 : ℝ))) =
          i₁ (beta s)) := by
  obtain ⟨n, hn, beta, hbeta⟩ :=
    exists_boundary_loop_power_homotopy i₀ i₁ e₀ e₁ k hc alpha
  obtain ⟨H⟩ := exists_closed_curve_homotopy_of_conjugate
    ((boundaryLoopIterate alpha n).map i₀.continuous) (beta.map i₁.continuous) k hbeta
  obtain ⟨F, hF⟩ := exists_circle_cylinder_of_closed_curves H.toHomotopy.toContinuousMap
    (fun t => H.prop t)
  refine ⟨n, hn, beta, F, ?_, ?_⟩
  · intro s
    rw [hF]
    exact H.apply_zero s
  · intro s
    rw [hF]
    exact H.apply_one s

end PoincareConjecture.M76
