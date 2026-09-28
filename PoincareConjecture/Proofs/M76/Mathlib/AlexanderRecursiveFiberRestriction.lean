import PoincareConjecture.Proofs.M76.Mathlib.CollarCutMembership
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

theorem collar_fiber_mem_cut_iff_of_disjoint
    {E : Type*} [TopologicalSpace E] {B T s₀ s₁ : Set E} {upper : E → ℝ}
    (C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁) (hcover : T ⊆ s₀ ∪ s₁)
    (hdisj : T ∩ (s₀ ∩ s₁) = ∅)
    (p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)}) :
    ((C p : E) ∈ s₀ ↔ (p : E × ℝ).1 ∈ s₀) ∧
      ((C p : E) ∈ s₁ ↔ (p : E × ℝ).1 ∈ s₁) := by
  let x := (p : E × ℝ).1
  let I := Icc (0 : ℝ) (upper x)
  let P : I → {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} :=
    fun z => ⟨(x, z), p.property.1, z.property⟩
  let f : I → E := fun z => C (P z)
  have hP : Continuous P :=
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _
  have hf : Continuous f := continuous_subtype_val.comp (C.continuous.comp hP)
  let : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hpre : IsPreconnected (range f) := isPreconnected_range hf
  have hrange : range f ⊆ T := by
    rintro y ⟨z, rfl⟩
    exact (C (P z)).property
  have hcut : range f ∩ (s₀ ∩ s₁) = ∅ :=
    eq_empty_iff_forall_notMem.mpr (fun _ hx =>
      (hdisj.subset ⟨hrange hx.1, hx.2⟩).elim)
  have hmem : (C p : E) ∈ range f := ⟨⟨(p : E × ℝ).2, p.property.2⟩, rfl⟩
  have hx : x ∈ range f := by
    let z : I := ⟨0, le_rfl, p.property.2.1.trans p.property.2.2⟩
    exact ⟨z, hbottom (P z) rfl⟩
  exact hpre.mem_closed_cut_iff hs₀ hs₁ (hrange.trans hcover) hcut hmem hx

theorem IsFinitePL.restrictSubsets_of_target
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {s b : Set E} {t c : Set F} {e : s ≃ₜ t} (he : e.IsFinitePL)
    (hb : b ⊆ s) (hc : c ⊆ t)
    (hmem : ∀ x : s, (x : E) ∈ b ↔ (e x : F) ∈ c)
    (J : SimplicialComplex ℝ F) (hJ : J.faces.Finite) (hspace : J.space = c) :
    (e.restrictSubsets hb hc hmem).IsFinitePL := by
  have hinv (y : t) : (y : F) ∈ c ↔ (e.symm y : E) ∈ b := by
    simpa only [e.apply_symm_apply] using (hmem (e.symm y)).symm
  let G := e.symm.restrictSubsets hc hb hinv
  have hG : G.IsFinitePL := he.symm.restrictSubsets hc hb hinv J hJ hspace
  have heq : G.symm = e.restrictSubsets hb hc hmem := by
    ext x
    rfl
  exact heq ▸ hG.symm

end Homeomorph
