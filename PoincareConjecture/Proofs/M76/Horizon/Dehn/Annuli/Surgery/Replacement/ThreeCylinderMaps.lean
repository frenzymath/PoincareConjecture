import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.CylinderMapGluing



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "Cyl" => (Set.prod Q J : Set E)
local notation "Left" => (Set.prod Q (Icc (-1 : ℝ) (-(1 / 2 : ℝ))) : Set E)
local notation "Middle" => (Set.prod Q (Icc (-(1 / 2 : ℝ)) 0) : Set E)
local notation "Right" => (Set.prod Q (Icc (0 : ℝ) 1) : Set E)

theorem exists_three_cylinder_map_gluing
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (f₀ f₁ f₂ : E → X)
    (hf₀ : PolyhedralPLInCharts e f₀ Cyl)
    (hf₁ : PolyhedralPLInCharts e f₁ Cyl)
    (hf₂ : PolyhedralPLInCharts e f₂ Cyl)
    (q₀ q₁ : Q ≃ₜ Q) (hq₀ : q₀.IsFinitePL) (hq₁ : q₁.IsFinitePL)
    (hseam₀ : ∀ u : Q, f₀ (u, 1) = f₁ (q₀ u, -1))
    (hseam₁ : ∀ u : Q, f₁ (u, 1) = f₂ (q₁ u, -1)) :
    ∃ (g : E → X) (j₀ : Cyl ≃ₜ Left) (j₁ : Cyl ≃ₜ Middle)
      (j₂ : Cyl ≃ₜ Right),
      PolyhedralPLInCharts e g Cyl ∧ j₀.IsFinitePL ∧ j₁.IsFinitePL ∧ j₂.IsFinitePL ∧
      (∀ x : Cyl, (j₀ x).val = (x.val.1, (x.val.2 - 3) / 4)) ∧
      (∀ x : Cyl, (j₁ x).val =
        ((q₀.symm ⟨x.val.1, x.property.1⟩ : V2), (x.val.2 - 1) / 4)) ∧
      (∀ x : Cyl, (j₂ x).val =
        (((q₀.trans q₁).symm ⟨x.val.1, x.property.1⟩ : V2), (x.val.2 + 1) / 2)) ∧
      (∀ x : Cyl, g (j₀ x) = f₀ x) ∧
      (∀ x : Cyl, g (j₁ x) = f₁ x) ∧
      (∀ x : Cyl, g (j₂ x) = f₂ x) ∧
      (∀ u : Q, g (u, -1) = f₀ (u, -1)) ∧
      (∀ u : Q, g (u, 1) = f₂ (q₁ (q₀ u), 1)) ∧
      g '' Cyl = (f₀ '' Cyl ∪ f₁ '' Cyl) ∪ f₂ '' Cyl := by
  obtain ⟨a, l₀, r₀, ha, _, _, hl₀, hr₀, hal, har, ha0, ha1, haimage, _⟩ :=
    exists_cylinder_map_gluing e hcompat f₀ f₁ hf₀ hf₁ q₀ hq₀ hseam₀
  have hseam (u : Q) : a (u, 1) = f₂ ((q₀.trans q₁) u, -1) :=
    (ha1 u).trans (hseam₁ (q₀ u))
  obtain ⟨g, l₁, r₁, hg, _, hr₁PL, hl₁, hr₁, hgl, hgr,
    hg0, hg1, hgimage, _⟩ :=
    exists_cylinder_map_gluing e hcompat a f₂ ha hf₂
      (q₀.trans q₁) (hq₀.trans hq₁) hseam
  obtain ⟨j₀, hj₀, hj₀v⟩ := exists_cylinder_band_chart (Homeomorph.refl Q)
    finitePL_square_rim_refl (-1) (-(1 / 2 : ℝ)) (by norm_num)
  obtain ⟨j₁, hj₁, hj₁v⟩ := exists_cylinder_band_chart q₀.symm hq₀.symm
    (-(1 / 2 : ℝ)) 0 (by norm_num)
  have hv₀ (x : Cyl) : (j₀ x).val = (x.val.1, (x.val.2 - 3) / 4) := by
    rw [hj₀v]
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have hv₁ (x : Cyl) : (j₁ x).val =
      ((q₀.symm ⟨x.val.1, x.property.1⟩ : V2), (x.val.2 - 1) / 4) := by
    rw [hj₁v]
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have hleft (x : Cyl) : (l₀ x : E) ∈ Cyl :=
    ⟨(l₀ x).property.1, (l₀ x).property.2.1, le_trans (l₀ x).property.2.2 (by norm_num)⟩
  have hright (x : Cyl) : (r₀ x : E) ∈ Cyl :=
    ⟨(r₀ x).property.1, le_trans (by norm_num) (r₀ x).property.2.1, (r₀ x).property.2.2⟩
  have hcopy₀ (x : Cyl) : (j₀ x : E) = l₁ ⟨l₀ x, hleft x⟩ := by
    rw [hv₀, hl₁, hl₀]
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have hcopy₁ (x : Cyl) : (j₁ x : E) = l₁ ⟨r₀ x, hright x⟩ := by
    rw [hv₁, hl₁, hr₀]
    apply Prod.ext
    · rfl
    · dsimp
      ring
  refine ⟨g, j₀, j₁, r₁, hg, hj₀, hj₁, hr₁PL, hv₀, hv₁, hr₁, ?_, ?_, hgr,
    ?_, hg1, ?_⟩
  · intro x
    rw [hcopy₀, hgl]
    exact hal x
  · intro x
    rw [hcopy₁, hgl]
    exact har x
  · intro u
    exact (hg0 u).trans (ha0 u)
  · exact hgimage.trans (congrArg (fun T : Set X ↦ T ∪ f₂ '' Cyl) haimage)

end PoincareConjecture.M76.Dehn.Annuli
