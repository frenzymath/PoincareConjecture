import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Mathlib.ConvexSubtypePaths










set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Dehn

local notation "I01" => Icc (0 : ℝ) 1

private theorem interval_parameter_mem_endpoints
    {E : Type*} [TopologicalSpace E] {U : Set E} {a b : E}
    (p : I01 ≃ₜ U) (hp0 : (p (0 : unitInterval) : E) = a)
    (hp1 : (p (1 : unitInterval) : E) = b) (t : I01) :
    (p t : E) ∈ ({a, b} : Set E) ↔ t = 0 ∨ t = 1 := by
  rw [← hp0, ← hp1]
  simp only [mem_insert_iff, mem_singleton_iff, Subtype.coe_inj, p.injective.eq_iff]




theorem exists_prescribed_two_interval_homeomorph
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U V : Set E} {W Z : Set F} {a b : E} {c d : F}
    (hUV : U ∩ V = {a, b}) (hWZ : W ∩ Z = {c, d})
    (p0 : I01 ≃ₜ U) (p1 : I01 ≃ₜ V)
    (q0 : I01 ≃ₜ W) (q1 : I01 ≃ₜ Z)
    (hp0 : p0.IsFinitePL) (hp1 : p1.IsFinitePL)
    (hq0 : q0.IsFinitePL) (hq1 : q1.IsFinitePL)
    (hp00 : (p0 (0 : unitInterval) : E) = a)
    (hp01 : (p0 (1 : unitInterval) : E) = b)
    (hp10 : (p1 (0 : unitInterval) : E) = a)
    (hp11 : (p1 (1 : unitInterval) : E) = b)
    (hq00 : (q0 (0 : unitInterval) : F) = c)
    (hq01 : (q0 (1 : unitInterval) : F) = d)
    (hq10 : (q1 (0 : unitInterval) : F) = c)
    (hq11 : (q1 (1 : unitInterval) : F) = d) :
    ∃ H : (U ∪ V : Set E) ≃ₜ (W ∪ Z : Set F), H.IsFinitePL ∧
      (∀ t : I01, (H ⟨p0 t, Or.inl (p0 t).property⟩ : F) = q0 t) ∧
      (∀ t : I01, (H ⟨p1 t, Or.inr (p1 t).property⟩ : F) = q1 t) := by
  let e := p0.symm.trans q0
  let f := p1.symm.trans q1
  have hoverlap (x : U) : (x : E) ∈ V ↔ (e x : F) ∈ Z := by
    obtain ⟨t, rfl⟩ := p0.surjective x
    have hleft : (p0 t : E) ∈ V ↔ (p0 t : E) ∈ ({a, b} : Set E) := by
      rw [← hUV]
      simp only [mem_inter_iff, (p0 t).property, true_and]
    have hright : (q0 t : F) ∈ Z ↔ (q0 t : F) ∈ ({c, d} : Set F) := by
      rw [← hWZ]
      simp only [mem_inter_iff, (q0 t).property, true_and]
    simpa only [e, Homeomorph.trans_apply, p0.symm_apply_apply] using
      hleft.trans ((interval_parameter_mem_endpoints p0 hp00 hp01 t).trans
        ((interval_parameter_mem_endpoints q0 hq00 hq01 t).symm.trans hright.symm))
  have hagree (x : E) (hxU : x ∈ U) (hxV : x ∈ V) :
      (e ⟨x, hxU⟩ : F) = f ⟨x, hxV⟩ := by
    have hx : x ∈ ({a, b} : Set E) := hUV.subset ⟨hxU, hxV⟩
    rcases hx with hx | hx
    · have h0 : (⟨x, hxU⟩ : U) = p0 0 := Subtype.ext (hx.trans hp00.symm)
      have h1 : (⟨x, hxV⟩ : V) = p1 0 := Subtype.ext (hx.trans hp10.symm)
      simp only [h0, h1, e, f, Homeomorph.trans_apply,
        p0.symm_apply_apply, p1.symm_apply_apply, hq00, hq10]
    · have h0 : (⟨x, hxU⟩ : U) = p0 1 := Subtype.ext (hx.trans hp01.symm)
      have h1 : (⟨x, hxV⟩ : V) = p1 1 := Subtype.ext (hx.trans hp11.symm)
      simp only [h0, h1, e, f, Homeomorph.trans_apply,
        p0.symm_apply_apply, p1.symm_apply_apply, hq01, hq11]
  obtain ⟨H, hH, h0, h1⟩ := Homeomorph.exists_union_finitePL e f
    (hp0.symm.trans hq0) (hp1.symm.trans hq1) hoverlap hagree
  refine ⟨H, hH, ?_, ?_⟩
  · intro t
    simpa only [e, Homeomorph.trans_apply, p0.symm_apply_apply] using h0 (p0 t)
  · intro t
    simpa only [f, Homeomorph.trans_apply, p1.symm_apply_apply] using h1 (p1 t)




theorem homotopic_of_interval_chart
    {X : Type*} [TopologicalSpace X] (e : I01 ≃ₜ X)
    {a b : X} (p q : Path a b) : p.Homotopic q := by
  have h := Path.homotopic_of_convex_range (convex_Icc (0 : ℝ) 1) Subset.rfl
    (p.map e.symm.continuous) (q.map e.symm.continuous)
    (fun t => (e.symm (p t)).property) (fun t => (e.symm (q t)).property)
  have hback := h.map ⟨e, e.continuous⟩
  have hcast := hback.pathCast (e.apply_symm_apply a).symm (e.apply_symm_apply b).symm
  have hp : ((p.map e.symm.continuous).map e.continuous).cast
      (e.apply_symm_apply a).symm (e.apply_symm_apply b).symm = p := by
    apply Path.ext
    funext t
    exact e.apply_symm_apply (p t)
  have hq : ((q.map e.symm.continuous).map e.continuous).cast
      (e.apply_symm_apply a).symm (e.apply_symm_apply b).symm = q := by
    apply Path.ext
    funext t
    exact e.apply_symm_apply (q t)
  simpa only [hp, hq] using hcast

end PoincareConjecture.M76.Dehn
