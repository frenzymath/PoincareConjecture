import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.CircleCoordinates.SourceAnnulus
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CubePrismBoundary



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Cyl" => (Q ×ˢ I : Set (V2 × ℝ))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem exists_cylinder_level_chart {T : Set E} (c : Cyl ≃ₜ T) (hc : c.IsFinitePL)
    (v : I) :
    ∃ (B : Set E) (gamma : Q ≃ₜ B), gamma.IsFinitePL ∧ B ⊆ T ∧
      (∀ u : Q, (gamma u : E) = c ⟨(u, v), u.property, v.property⟩) ∧
      ∀ x : Cyl, (c x : E) ∈ B ↔ x.val.2 = v := by
  obtain ⟨F, hF, hFv⟩ := hc
  let a : V2 →ᴬ[ℝ] (V2 × ℝ) :=
    (ContinuousAffineMap.id ℝ V2).prod (ContinuousAffineMap.const ℝ V2 (v : ℝ))
  obtain ⟨K, hK, hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
  have ha : FinitePiecewiseAffineOn a Q :=
    ⟨K, hK, hKs, K.affineOnFaces_affine a⟩
  have hamap : MapsTo a Q Cyl := fun _ hu ↦ ⟨hu, v.property⟩
  have hFa : FinitePiecewiseAffineOn (F ∘ a) Q := hF.comp ha hamap
  have hFi : InjOn (F ∘ a) Q := by
    intro u hu w hw h
    have heq : c ⟨(u, v), hu, v.property⟩ = c ⟨(w, v), hw, v.property⟩ :=
      Subtype.ext ((hFv ⟨(u, v), hu, v.property⟩).trans
        (h.trans (hFv ⟨(w, v), hw, v.property⟩).symm))
    exact congrArg (fun x : Cyl ↦ x.val.1) (c.injective heq)
  obtain ⟨gamma, hgamma, hvalue⟩ := hFa.exists_homeomorph_image hFi
  refine ⟨(F ∘ a) '' Q, gamma, hgamma, ?_, ?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    change F (u, v) ∈ T
    rw [← hFv ⟨(u, v), hu, v.property⟩]
    exact (c _).property
  · intro u
    exact (hvalue u).trans (hFv ⟨(u, v), u.property, v.property⟩).symm
  · intro x
    constructor
    · rintro ⟨u, hu, heq⟩
      have hcEq : c ⟨(u, v), hu, v.property⟩ = c x :=
        Subtype.ext ((hFv _).trans heq)
      exact (congrArg (fun y : Cyl ↦ y.val.2) (c.injective hcEq)).symm
    · intro hx
      refine ⟨x.val.1, x.property.1, ?_⟩
      have hx' : (⟨(x.val.1, v), x.property.1, v.property⟩ : Cyl) = x :=
        Subtype.ext (Prod.ext rfl hx.symm)
      exact (hFv _).symm.trans (congrArg (fun y : Cyl ↦ (c y : E)) hx')

theorem exists_cylinder_end_comparison {A B : Set E}
    (a : Cyl ≃ₜ A) (b : Cyl ≃ₜ B) (ha : a.IsFinitePL) (hb : b.IsFinitePL)
    (hab : ∀ x : Cyl, (a x : E) ∈ B ↔ x.val.2 = 1)
    (hba : ∀ x : Cyl, (b x : E) ∈ A ↔ x.val.2 = -1) :
    ∃ q : Q ≃ₜ Q, q.IsFinitePL ∧ ∀ u : Q,
      (b ⟨(q u, -1), (q u).property, le_rfl, by norm_num⟩ : E) =
        a ⟨(u, 1), u.property, by norm_num, le_rfl⟩ := by
  obtain ⟨S, g, hg, hSA, hgv, hS⟩ := exists_cylinder_level_chart a ha ⟨1, by norm_num⟩
  obtain ⟨T, f, hf, hTB, hfv, hT⟩ := exists_cylinder_level_chart b hb ⟨-1, by norm_num⟩
  have hST : S = T := by
    apply Subset.antisymm
    · intro z hz
      let x := a.symm ⟨z, hSA hz⟩
      have hax : (a x : E) = z := congrArg Subtype.val (a.apply_symm_apply _)
      have hzB : z ∈ B := hax ▸ (hab x).mpr ((hS x).mp (hax.symm ▸ hz))
      let y := b.symm ⟨z, hzB⟩
      have hby : (b y : E) = z := congrArg Subtype.val (b.apply_symm_apply _)
      exact hby ▸ (hT y).mpr ((hba y).mp (hby.symm ▸ hSA hz))
    · intro z hz
      let y := b.symm ⟨z, hTB hz⟩
      have hby : (b y : E) = z := congrArg Subtype.val (b.apply_symm_apply _)
      have hzA : z ∈ A := hby ▸ (hba y).mpr ((hT y).mp (hby.symm ▸ hz))
      let x := a.symm ⟨z, hzA⟩
      have hax : (a x : E) = z := congrArg Subtype.val (a.apply_symm_apply _)
      exact hax ▸ (hS x).mpr ((hab x).mp (hax.symm ▸ hTB hz))
  let g' := g.trans (Homeomorph.setCongr hST)
  let q := g'.trans f.symm
  refine ⟨q, (hg.setCongr rfl hST).trans hf.symm, ?_⟩
  intro u
  exact (hfv (q u)).symm.trans
    ((congrArg Subtype.val (f.apply_symm_apply (g' u))).trans (hgv u))

end PoincareConjecture.M76.Dehn.Annuli
