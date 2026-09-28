import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.Lifts.Scalar

set_option autoImplicit false

open scoped unitInterval

namespace PoincareConjecture.M76.LinearTorus

variable (p : ℝ) {X : Type*} [TopologicalSpace X] {S : Set X}

theorem exists_scalar_displacement_of_homotopyRel
    {f g : C(X, AddCircle p)} (H : f.HomotopyRel g S) :
    ∃ W : C(X, ℝ), (∀ x, (W x : AddCircle p) = g x - f x) ∧
      ∀ x ∈ S, W x = 0 := by
  let cov := AddCircle.isCoveringMap_coe p
  let D : C(unitInterval × X, AddCircle p) :=
    ⟨fun tx => H tx - f tx.2, H.continuous.sub (f.continuous.comp continuous_snd)⟩
  have hD0 (x : X) : D (0, x) = ((0 : ℝ) : AddCircle p) := by
    change H (0, x) - f x = ((0 : ℝ) : AddCircle p)
    rw [H.apply_zero, sub_self, AddCircle.coe_zero]
  let L : C(unitInterval × X, ℝ) :=
    cov.liftHomotopy D (ContinuousMap.const X 0) hD0
  have hL (t : unitInterval) (x : X) : (L (t, x) : AddCircle p) = D (t, x) :=
    congrFun (cov.liftHomotopy_lifts D (ContinuousMap.const X 0) hD0) (t, x)
  have hL0 (x : X) : L (0, x) = 0 :=
    cov.liftHomotopy_zero D (ContinuousMap.const X 0) hD0 x
  refine ⟨L.comp ((ContinuousMap.const X 1).prodMk (ContinuousMap.id X)), ?_, ?_⟩
  · intro x
    change (L (1, x) : AddCircle p) = g x - f x
    rw [hL]
    change H (1, x) - f x = g x - f x
    rw [H.apply_one]
  · intro x hx
    change L (1, x) = 0
    have hconst := cov.const_of_comp
      (L.continuous.comp (continuous_id.prodMk continuous_const))
      (fun t t' => show (L (t, x) : AddCircle p) = (L (t', x) : AddCircle p) from by
        rw [hL, hL]
        change H (t, x) - f x = H (t', x) - f x
        rw [H.eq_fst t hx, H.eq_fst t' hx]) (1 : unitInterval) 0
    exact hconst.trans (hL0 x)

theorem exists_real_displacement_of_homotopyRel
    {f g : C(X, AddCircle p × AddCircle p)} (H : f.HomotopyRel g S) :
    ∃ W : C(X, ℝ × ℝ), (∀ x, quotientMap p (W x) = g x - f x) ∧
      ∀ x ∈ S, W x = 0 := by
  obtain ⟨W₁, hW₁, hS₁⟩ := exists_scalar_displacement_of_homotopyRel p
    (H.compContinuousMap ContinuousMap.fst)
  obtain ⟨W₂, hW₂, hS₂⟩ := exists_scalar_displacement_of_homotopyRel p
    (H.compContinuousMap ContinuousMap.snd)
  refine ⟨W₁.prodMk W₂, ?_, ?_⟩
  · intro x
    exact Prod.ext (hW₁ x) (hW₂ x)
  · intro x hx
    exact Prod.ext (hS₁ x hx) (hS₂ x hx)

theorem exists_real_displacement_of_homotopy
    {f g : C(X, AddCircle p × AddCircle p)} (H : f.Homotopy g) :
    ∃ W : C(X, ℝ × ℝ), ∀ x, quotientMap p (W x) = g x - f x := by
  let Hrel : f.HomotopyRel g ∅ := { H with prop' := by simp }
  obtain ⟨W, hW, _⟩ := exists_real_displacement_of_homotopyRel p Hrel
  exact ⟨W, hW⟩

end PoincareConjecture.M76.LinearTorus
