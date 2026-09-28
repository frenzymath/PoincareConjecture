import PoincareConjecture.Proofs.M76.Mathlib.RadialRescalingPlane
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph












set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]








theorem exists_radial_height_correction_with_ratio (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hrad : InjOn (NormedSpace.normalize : E → E) K.space)
    (φ : E → ℝ) (hφ : K.AffineOnFaces φ) (B C : E →ₗ[ℝ] ℝ)
    (hC : K.RespectsAffineHyperplane C.toAffineMap)
    (hneg : ∀ x ∈ K.vertices, φ x < 0 ↔ B x < 0)
    (hpos : ∀ x ∈ K.vertices, 0 < φ x ↔ 0 < B x) :
    ∃ (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) (f : E → E)
      (e : K.space ≃ₜ (K.radialRescale hlin hrad r hr).space),
      K.AffineOnFaces f ∧
      (∀ x : K.space, (e x : E) = f x) ∧
      EqOn f (fun x => r x • x) K.vertices ∧ e.IsFinitePL ∧
      (∀ x : K.space, B (e x) = φ x) ∧
      (∀ x : K.space, C (e x) = 0 ↔ C x = 0) ∧
      ∀ x, r x = if B x = 0 then 1 else φ x / B x := by
  classical
  let r : E → ℝ := fun x => if B x = 0 then 1 else φ x / B x
  have hzero (x : E) (hx : x ∈ K.vertices) (hBx : B x = 0) : φ x = 0 := by
    rcases lt_trichotomy (φ x) 0 with hn | he | hp
    · have h := (hneg x hx).mp hn
      rw [hBx] at h
      exact (lt_irrefl _ h).elim
    · exact he
    · have h := (hpos x hx).mp hp
      rw [hBx] at h
      exact (lt_irrefl _ h).elim
  have hr (x : E) (hx : x ∈ K.vertices) : 0 < r x := by
    dsimp only [r]
    split_ifs with hBx
    · exact zero_lt_one
    · rcases lt_or_gt_of_ne hBx with hn | hp
      · exact div_pos_of_neg_of_neg ((hneg x hx).mpr hn) hn
      · exact div_pos ((hpos x hx).mpr hp) hp
  have hvertexHeight (x : E) (hx : x ∈ K.vertices) : B (r x • x) = φ x := by
    rw [map_smul, smul_eq_mul]
    by_cases hBx : B x = 0
    · rw [hBx, mul_zero, hzero x hx hBx]
    · dsimp only [r]
      rw [if_neg hBx, div_mul_cancel₀ _ hBx]
  obtain ⟨f, _, e, hf, _, hfv, hef, _⟩ :=
    K.exists_radialRescale_homeomorph hK hlin hrad r hr
  let Bc := B.toContinuousLinearMap.toContinuousAffineMap
  have hheight : EqOn (B ∘ f) φ K.space := by
    apply (hf.postcomp Bc).eqOn_of_eqOn_vertices hφ
    intro x hx
    change B (f x) = φ x
    rw [hfv hx]
    exact hvertexHeight x hx
  have hplane := hf.linear_zero_iff_of_positive_vertex_rescaling r hr hfv C hC
  refine ⟨r, hr, f, e, hf, hef, hfv, ⟨f, hf.finitePiecewiseAffineOn hK, hef⟩,
    ?_, ?_, fun _ => rfl⟩
  · intro x
    rw [hef]
    exact hheight x.property
  · intro x
    rw [hef]
    exact hplane x x.property






theorem exists_radial_height_correction (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hrad : InjOn (NormedSpace.normalize : E → E) K.space)
    (φ : E → ℝ) (hφ : K.AffineOnFaces φ) (B C : E →ₗ[ℝ] ℝ)
    (hC : K.RespectsAffineHyperplane C.toAffineMap)
    (hneg : ∀ x ∈ K.vertices, φ x < 0 ↔ B x < 0)
    (hpos : ∀ x ∈ K.vertices, 0 < φ x ↔ 0 < B x) :
    ∃ (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x) (f : E → E)
      (e : K.space ≃ₜ (K.radialRescale hlin hrad r hr).space),
      K.AffineOnFaces f ∧
      (∀ x : K.space, (e x : E) = f x) ∧
      EqOn f (fun x => r x • x) K.vertices ∧ e.IsFinitePL ∧
      (∀ x : K.space, B (e x) = φ x) ∧
      (∀ x : K.space, C (e x) = 0 ↔ C x = 0) := by
  obtain ⟨r, hr, f, e, hf, hef, hfv, he, hheight, hplane, _⟩ :=
    K.exists_radial_height_correction_with_ratio hK hlin hrad φ hφ B C hC hneg hpos
  exact ⟨r, hr, f, e, hf, hef, hfv, he, hheight, hplane⟩

end Geometry.SimplicialComplex
