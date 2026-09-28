import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PeriodCircleLoop
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.ContinuousOn

set_option autoImplicit false

open Set
open scoped unitInterval

namespace Poincare.Topology

variable {E Y : Type*} [TopologicalSpace E] [TopologicalSpace Y]

theorem exists_circle_map_of_product_handle {P H : Set E}
    (hP : IsClosed P) (hH : IsClosed H)
    (C : (Y × unitInterval) ≃ₜ H)
    (hattach : ∀ z : Y × unitInterval,
      (C z : E) ∈ P ↔ z.2 = 0 ∨ z.2 = 1) :
    ∃ f : C((P ∪ H : Set E), AddCircle (1 : ℝ)),
      (∀ x : P, f ⟨x, Or.inl x.property⟩ = 0) ∧
      ∀ z : Y × unitInterval,
        f ⟨C z, Or.inr (C z).property⟩ = ((z.2 : ℝ) : AddCircle (1 : ℝ)) := by
  classical
  let g : E → AddCircle (1 : ℝ) := fun x =>
    if hx : x ∈ H then (((C.symm ⟨x, hx⟩).2 : ℝ) : AddCircle (1 : ℝ)) else 0
  have hgH (z : Y × unitInterval) :
      g (C z) = ((z.2 : ℝ) : AddCircle (1 : ℝ)) := by
    simp only [g, dif_pos (C z).property, C.symm_apply_apply]
  have hgP (x : E) (hx : x ∈ P) : g x = 0 := by
    by_cases hxH : x ∈ H
    · let z := C.symm ⟨x, hxH⟩
      have hz : (C z : E) = x := congrArg Subtype.val (C.apply_symm_apply ⟨x, hxH⟩)
      rw [← hz, hgH]
      rcases (hattach z).mp (hz.symm ▸ hx) with h0 | h1
      · simp [h0]
      · simp [h1]
    · simp [g, hxH]
  have hgPc : ContinuousOn g P := continuousOn_const.congr (fun x hx => hgP x hx)
  have hgHc : ContinuousOn g H := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : H => g x)
    have heq : (fun x : H => g x) =
        (fun x : H => (((C.symm x).2 : ℝ) : AddCircle (1 : ℝ))) := by
      funext x
      simp [g, x.property]
    rw [heq]
    exact (AddCircle.continuous_mk' (1 : ℝ)).comp
      (continuous_subtype_val.comp (continuous_snd.comp C.symm.continuous))
  refine ⟨⟨fun x => g x, (hgPc.union_of_isClosed hgHc hP hH).domRestrict⟩,
    fun x => hgP x x.property, hgH⟩

theorem exists_nontrivial_loop_of_product_handle [Nonempty Y] {P H : Set E}
    (hP : IsClosed P) (hH : IsClosed H) (hPc : IsPathConnected P)
    (C : (Y × unitInterval) ≃ₜ H)
    (hattach : ∀ z : Y × unitInterval,
      (C z : E) ∈ P ↔ z.2 = 0 ∨ z.2 = 1) :
    ∃ f : C((P ∪ H : Set E), AddCircle (1 : ℝ)),
      (∀ x : P, f ⟨x, Or.inl x.property⟩ = 0) ∧
      (∀ z : Y × unitInterval,
        f ⟨C z, Or.inr (C z).property⟩ = ((z.2 : ℝ) : AddCircle (1 : ℝ))) ∧
      ∃ (x : (P ∪ H : Set E)) (hx : f x = 0) (gamma : Path x x),
        ((gamma.map f.continuous).cast hx.symm hx.symm).Homotopic
          (AddCircle.periodLoop 1) ∧
        ¬ gamma.Homotopic (Path.refl x) := by
  classical
  obtain ⟨f, hfP, hfH⟩ := exists_circle_map_of_product_handle hP hH C hattach
  let y : Y := Classical.choice inferInstance
  let x0 : (P ∪ H : Set E) := ⟨C (y, 0), Or.inr (C (y, 0)).property⟩
  let x1 : (P ∪ H : Set E) := ⟨C (y, 1), Or.inr (C (y, 1)).property⟩
  have hx0P : (x0 : E) ∈ P := (hattach (y, 0)).mpr (Or.inl rfl)
  have hx1P : (x1 : E) ∈ P := (hattach (y, 1)).mpr (Or.inr rfl)
  have hf0 : f x0 = 0 := hfP ⟨x0, hx0P⟩
  have hf1 : f x1 = 0 := hfP ⟨x1, hx1P⟩
  let core : Path x0 x1 := {
    toFun := fun t => ⟨C (y, t), Or.inr (C (y, t)).property⟩
    continuous_toFun := (continuous_subtype_val.comp
      (C.continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk _
    source' := rfl
    target' := rfl }
  let : PathConnectedSpace P := isPathConnected_iff_pathConnectedSpace.mp hPc
  let backP : Path (⟨x1, hx1P⟩ : P) ⟨x0, hx0P⟩ := PathConnectedSpace.somePath _ _
  let back : Path x1 x0 := backP.map
    (show Continuous (fun x : P => (⟨x, Or.inl x.property⟩ : (P ∪ H : Set E))) from
      continuous_subtype_val.subtype_mk _)
  have hcore : (core.map f.continuous).cast hf0.symm hf1.symm =
      AddCircle.periodLoop 1 := by
    ext t
    change f ⟨C (y, t), Or.inr (C (y, t)).property⟩ = _
    simpa only [AddCircle.periodLoop, Path.coe_mk_mk, mul_one] using hfH (y, t)
  have hback : (back.map f.continuous).cast hf1.symm hf0.symm = Path.refl 0 := by
    ext t
    exact hfP (backP t)
  let gamma := core.trans back
  have hgamma : (gamma.map f.continuous).cast hf0.symm hf0.symm =
      (AddCircle.periodLoop 1).trans (Path.refl 0) := by
    rw [Path.map_trans, Path.cast_trans _ _ hf0.symm hf1.symm hf0.symm, hcore, hback]
  have hperiod : ((gamma.map f.continuous).cast hf0.symm hf0.symm).Homotopic
      (AddCircle.periodLoop 1) := by
    rw [hgamma]
    exact Path.Homotopic.trans_refl _
  refine ⟨f, hfP, hfH, x0, hf0, gamma, hperiod, ?_⟩
  intro hnull
  have h := (hnull.map f).pathCast hf0.symm hf0.symm
  have hrefl : ((Path.refl x0).map f.continuous).cast hf0.symm hf0.symm =
      Path.refl 0 := by
    ext t
    exact hf0
  rw [hrefl] at h
  exact AddCircle.periodLoop_not_homotopic_refl 1 (hperiod.symm.trans h)

theorem not_simplyConnectedSpace_of_product_handle [Nonempty Y] {P H : Set E}
    (hP : IsClosed P) (hH : IsClosed H) (hPc : IsPathConnected P)
    (C : (Y × unitInterval) ≃ₜ H)
    (hattach : ∀ z : Y × unitInterval,
      (C z : E) ∈ P ↔ z.2 = 0 ∨ z.2 = 1) :
    ¬ SimplyConnectedSpace (P ∪ H : Set E) := by
  obtain ⟨_, _, _, x, _, gamma, _, hnontrivial⟩ :=
    exists_nontrivial_loop_of_product_handle hP hH hPc C hattach
  intro h
  exact hnontrivial ((simply_connected_iff_loops_nullhomotopic.mp h).2 x gamma)

end Poincare.Topology
