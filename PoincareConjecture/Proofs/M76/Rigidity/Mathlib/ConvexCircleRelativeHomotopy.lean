import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.AddCircle.Real

set_option autoImplicit false

open Set unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {C : Set E} {A : Set C}

theorem Convex.exists_circle_difference_lift (hC : Convex ℝ C)
    (hA : IsPreconnected A) (b : C) (hb : b ∈ A)
    (p : ℝ) [Fact (0 < p)] (f : C(C × AddCircle p, AddCircle p))
    (hf : ∀ x ∈ A, ∀ z : AddCircle p, f (x, z) = z) :
    ∃ l : C(C × AddCircle p, ℝ),
      (∀ w, (l w : AddCircle p) = f w - w.2) ∧
      ∀ x ∈ A, ∀ z : AddCircle p, l (x, z) = 0 := by
  let c : C(I × C, C) :=
    ⟨fun w => ⟨(1 - (w.1 : ℝ)) • (b : E) + (w.1 : ℝ) • (w.2 : E),
      hC b.property w.2.property (sub_nonneg.mpr w.1.property.2)
        w.1.property.1 (sub_add_cancel _ _)⟩, by fun_prop⟩
  have hc0 (x : C) : c (0, x) = b := by
    apply Subtype.ext
    simp [c]
  have hc1 (x : C) : c (1, x) = x := by
    apply Subtype.ext
    simp [c]
  have hcb (s : I) : c (s, b) = b := by
    apply Subtype.ext
    change (1 - (s : ℝ)) • (b : E) + (s : ℝ) • (b : E) = b
    rw [← add_smul, sub_add_cancel, one_smul]
  let H : C(I × (C × AddCircle p), AddCircle p) :=
    ⟨fun w => f (c (w.1, w.2.1), w.2.2) - w.2.2, by fun_prop⟩
  let z : C(C × AddCircle p, ℝ) := ContinuousMap.const _ 0
  have hH0 (w : C × AddCircle p) : H (0, w) = (z w : AddCircle p) := by
    change f (c (0, w.1), w.2) - w.2 = 0
    rw [hc0, hf b hb, sub_self]
  let cov := AddCircle.isCoveringMap_coe p
  let T := cov.liftHomotopy H z hH0
  have hT (s : I) (w : C × AddCircle p) :
      (T (s, w) : AddCircle p) = H (s, w) :=
    congr_fun (cov.liftHomotopy_lifts H z hH0) (s, w)
  have hT0 (w : C × AddCircle p) : T (0, w) = 0 :=
    cov.liftHomotopy_zero H z hH0 w
  have hTb (s : I) (y : AddCircle p) : T (s, (b, y)) = 0 := by
    have hcont : Continuous (fun t : I => T (t, (b, y))) :=
      T.continuous.comp (continuous_id.prodMk continuous_const)
    have hconst := cov.const_of_comp hcont (fun t t' => by
      rw [hT, hT]
      change f (c (t, b), y) - y = f (c (t', b), y) - y
      rw [hcb, hcb]) s 0
    exact hconst.trans (hT0 (b, y))
  let l : C(C × AddCircle p, ℝ) :=
    T.comp ((ContinuousMap.const _ (1 : I)).prodMk (ContinuousMap.id _))
  have hl (w : C × AddCircle p) : (l w : AddCircle p) = f w - w.2 := by
    change (T (1, w) : AddCircle p) = _
    rw [hT]
    change f (c (1, w.1), w.2) - w.2 = f w - w.2
    rw [hc1]
  refine ⟨l, hl, ?_⟩
  intro x hx y
  have hcont : Continuous (fun a : C => l (a, y)) :=
    l.continuous.comp (continuous_id.prodMk continuous_const)
  have hconst := cov.constOn_of_comp hA hcont.continuousOn
    (fun a ha a' ha' => by rw [hl, hl, hf a ha, hf a' ha']) hx hb
  exact hconst.trans (hTb 1 y)

theorem Convex.exists_homotopyRel_circle_product (hC : Convex ℝ C)
    (hA : IsPreconnected A) (b : C) (hb : b ∈ A)
    (p : ℝ) [Fact (0 < p)] (f : C(C × AddCircle p, C × AddCircle p))
    (hf : ∀ x ∈ A, ∀ z : AddCircle p, f (x, z) = (x, z)) :
    Nonempty ((ContinuousMap.id (C × AddCircle p)).HomotopyRel f (A ×ˢ univ)) := by
  let f2 : C(C × AddCircle p, AddCircle p) :=
    ⟨fun w => (f w).2, continuous_snd.comp f.continuous⟩
  obtain ⟨l, hl, hlA⟩ := hC.exists_circle_difference_lift hA b hb p f2
    (fun x hx z => congrArg Prod.snd (hf x hx z))
  refine ⟨{
    toFun := fun w =>
      (⟨(1 - (w.1 : ℝ)) • (w.2.1 : E) + (w.1 : ℝ) • ((f w.2).1 : E),
        hC w.2.1.property (f w.2).1.property (sub_nonneg.mpr w.1.property.2)
          w.1.property.1 (sub_add_cancel _ _)⟩,
        w.2.2 + (((w.1 : ℝ) * l w.2 : ℝ) : AddCircle p))
    continuous_toFun := by fun_prop
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro w
    apply Prod.ext
    · apply Subtype.ext
      simp
    · simp
  · intro w
    apply Prod.ext
    · apply Subtype.ext
      simp
    · change w.2 + (((1 : ℝ) * l w : ℝ) : AddCircle p) = (f w).2
      rw [one_mul, hl]
      change w.2 + ((f w).2 - w.2) = (f w).2
      abel
  · intro t w hw
    apply Prod.ext
    · apply Subtype.ext
      change (1 - (t : ℝ)) • (w.1 : E) + (t : ℝ) • ((f w).1 : E) = w.1
      rw [hf w.1 hw.1 w.2]
      rw [← add_smul, sub_add_cancel, one_smul]
    · change w.2 + (((t : ℝ) * l w : ℝ) : AddCircle p) = w.2
      rw [hlA w.1 hw.1 w.2, mul_zero]
      simp
