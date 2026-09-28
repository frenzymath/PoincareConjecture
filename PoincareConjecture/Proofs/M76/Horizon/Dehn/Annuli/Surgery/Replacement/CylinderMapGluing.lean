import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Replacement.CylinderBands
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.TargetMapPasting

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "Cyl" => (Q ×ˢ J : Set E)
local notation "Left" => (Set.prod Q (Icc (-1 : ℝ) 0) : Set E)
local notation "Right" => (Set.prod Q (Icc (0 : ℝ) 1) : Set E)

theorem exists_cylinder_map_gluing
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X F)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid F)
    (f₀ f₁ : E → X) (hf₀ : PolyhedralPLInCharts e f₀ Cyl)
    (hf₁ : PolyhedralPLInCharts e f₁ Cyl)
    (q : Q ≃ₜ Q) (hq : q.IsFinitePL)
    (hseam : ∀ u : Q, f₀ (u, 1) = f₁ (q u, -1)) :
    ∃ (g : E → X) (l : Cyl ≃ₜ Left) (r : Cyl ≃ₜ Right),
      PolyhedralPLInCharts e g Cyl ∧ l.IsFinitePL ∧ r.IsFinitePL ∧
      (∀ x : Cyl, (l x).val = (x.val.1, (x.val.2 - 1) / 2)) ∧
      (∀ x : Cyl, (r x).val = ((q.symm ⟨x.val.1, x.property.1⟩ : V2),
        (x.val.2 + 1) / 2)) ∧
      (∀ x : Cyl, g (l x) = f₀ x) ∧
      (∀ x : Cyl, g (r x) = f₁ x) ∧
      (∀ u : Q, g (u, -1) = f₀ (u, -1)) ∧
      (∀ u : Q, g (u, 1) = f₁ (q u, 1)) ∧
      g '' Cyl = f₀ '' Cyl ∪ f₁ '' Cyl ∧
      ∀ W : Set X, Cyl ∩ g ⁻¹' W =
        (fun x : Cyl ↦ (l x : E)) '' {x | f₀ x ∈ W} ∪
        (fun x : Cyl ↦ (r x : E)) '' {x | f₁ x ∈ W} := by
  obtain ⟨l, hl, hlv⟩ := exists_cylinder_band_chart (Homeomorph.refl Q)
    finitePL_square_rim_refl (-1) 0 (by norm_num)
  obtain ⟨r, hr, hrv⟩ := exists_cylinder_band_chart q.symm hq.symm 0 1 (by norm_num)
  have hlval (x : Cyl) : (l x).val = (x.val.1, (x.val.2 - 1) / 2) := by
    rw [hlv]
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have hrval (x : Cyl) : (r x).val =
      ((q.symm ⟨x.val.1, x.property.1⟩ : V2), (x.val.2 + 1) / 2) := by
    simpa using hrv x
  obtain ⟨il, hil, hilv⟩ := hl.symm
  obtain ⟨ir, hir, hirv⟩ := hr.symm
  have hilm : MapsTo il Left Cyl := by
    intro x hx
    rw [← hilv ⟨x, hx⟩]
    exact (l.symm ⟨x, hx⟩).property
  have hirm : MapsTo ir Right Cyl := by
    intro x hx
    rw [← hirv ⟨x, hx⟩]
    exact (r.symm ⟨x, hx⟩).property
  have hilcopy := hil
  have hircopy := hir
  obtain ⟨K, hK, hKs, _⟩ := hilcopy
  obtain ⟨N, hN, hNs, _⟩ := hircopy
  have hp₀ : PolyhedralPLInCharts e (f₀ ∘ il) K.space :=
    hf₀.comp_finitePiecewiseAffineOn K hK (by simpa only [hKs] using hil)
      (fun _ hx ↦ hilm (hKs.subset hx))
  have hp₁ : PolyhedralPLInCharts e (f₁ ∘ ir) N.space :=
    hf₁.comp_finitePiecewiseAffineOn N hN (by simpa only [hNs] using hir)
      (fun _ hx ↦ hirm (hNs.subset hx))
  have hagree (x : E) (hxl : x ∈ Left) (hxr : x ∈ Right) :
      f₀ (il x) = f₁ (ir x) := by
    have ht : x.2 = 0 := le_antisymm hxl.2.2 hxr.2.1
    have hle : l ⟨(x.1, 1), hxl.1, by norm_num, le_rfl⟩ = ⟨x, hxl⟩ := by
      apply Subtype.ext
      rw [hlval]
      exact Prod.ext rfl (by dsimp; linarith)
    have hre : r ⟨(q ⟨x.1, hxl.1⟩, -1), (q _).property, le_rfl, by norm_num⟩ =
        ⟨x, hxr⟩ := by
      apply Subtype.ext
      rw [hrval]
      apply Prod.ext
      · exact congrArg Subtype.val (q.symm_apply_apply _)
      · dsimp
        linarith
    rw [← hilv ⟨x, hxl⟩, ← hirv ⟨x, hxr⟩, ← hle, ← hre,
      l.symm_apply_apply, r.symm_apply_apply]
    exact hseam ⟨x.1, hxl.1⟩
  obtain ⟨g, hg, hgl, hgr⟩ := _root_.Dehn.exists_circle_attachment_map_union
    hcompat K N hK hN hp₀ hp₁
      (fun x hx hy ↦ hagree x (hKs.subset hx) (hNs.subset hy))
  have hunion : Left ∪ Right = Cyl := by
    ext x
    constructor
    · rintro (hx | hx) <;>
        exact ⟨hx.1, by linarith [hx.2.1], by linarith [hx.2.2]⟩
    · intro hx
      rcases le_total x.2 0 with ht | ht
      · exact Or.inl ⟨hx.1, hx.2.1, ht⟩
      · exact Or.inr ⟨hx.1, ht, hx.2.2⟩
  have hgv₀ (x : Cyl) : g (l x) = f₀ x := by
    rw [hgl (hKs.symm.subset (l x).property)]
    change f₀ (il (l x)) = _
    rw [← hilv, l.symm_apply_apply]
  have hgv₁ (x : Cyl) : g (r x) = f₁ x := by
    rw [hgr (hNs.symm.subset (r x).property)]
    change f₁ (ir (r x)) = _
    rw [← hirv, r.symm_apply_apply]
  refine ⟨g, l, r, ?_, hl, hr, hlval, hrval, hgv₀, hgv₁, ?_, ?_, ?_, ?_⟩
  · rw [hKs, hNs] at hg
    exact hunion ▸ hg
  · intro u
    have hv := hgv₀ ⟨(u, -1), u.property, le_rfl, by norm_num⟩
    rw [hlval] at hv
    norm_num at hv
    exact hv
  · intro u
    have hv := hgv₁ ⟨(q u, 1), (q u).property, by norm_num, le_rfl⟩
    rw [hrval] at hv
    simpa using hv
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hunion.symm.subset hx with hx | hx
      · exact Or.inl ⟨l.symm ⟨x, hx⟩, (l.symm ⟨x, hx⟩).property,
          (hgv₀ _).symm.trans (congrArg (fun z : Left ↦ g z) (l.apply_symm_apply _))⟩
      · exact Or.inr ⟨r.symm ⟨x, hx⟩, (r.symm ⟨x, hx⟩).property,
          (hgv₁ _).symm.trans (congrArg (fun z : Right ↦ g z) (r.apply_symm_apply _))⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨l ⟨x, hx⟩, hunion.subset (Or.inl (l ⟨x, hx⟩).property), hgv₀ _⟩
      · exact ⟨r ⟨x, hx⟩, hunion.subset (Or.inr (r ⟨x, hx⟩).property), hgv₁ _⟩
  · intro W
    ext x
    constructor
    · rintro ⟨hx, hgx⟩
      rcases hunion.symm.subset hx with hx | hx
      · refine Or.inl ⟨l.symm ⟨x, hx⟩, ?_, congrArg Subtype.val (l.apply_symm_apply _)⟩
        change f₀ (l.symm ⟨x, hx⟩) ∈ W
        rw [← hgv₀, l.apply_symm_apply]
        exact hgx
      · refine Or.inr ⟨r.symm ⟨x, hx⟩, ?_, congrArg Subtype.val (r.apply_symm_apply _)⟩
        change f₁ (r.symm ⟨x, hx⟩) ∈ W
        rw [← hgv₁, r.apply_symm_apply]
        exact hgx
    · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
      · refine ⟨hunion.subset (Or.inl (l y).property), ?_⟩
        change g (l y) ∈ W
        rwa [hgv₀]
      · refine ⟨hunion.subset (Or.inr (r y).property), ?_⟩
        change g (r y) ∈ W
        rwa [hgv₁]

end PoincareConjecture.M76.Dehn.Annuli
