import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Replacement.Seam
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.PrescribedTwoIntervalCircle
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_returning_disk_identification
    {X ι E F : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    {D₀ U₀ W₀ : Set E} {D₁ U₁ W₁ : Set F}
    {a b : E} {c d : F} {f : E → X} {g : F → X}
    (hD₀ : IsFinitePLBallPair (ℝ × ℝ) D₀ (U₀ ∪ W₀))
    (hD₁ : IsFinitePLBallPair (ℝ × ℝ) D₁ (U₁ ∪ W₁))
    (hU₀ : IsFinitePLBallPair ℝ U₀ {a, b})
    (hW₀ : IsFinitePLBallPair ℝ W₀ {a, b})
    (hU₁ : IsFinitePLBallPair ℝ U₁ {c, d})
    (hW₁ : IsFinitePLBallPair ℝ W₁ {c, d})
    (hinter₀ : U₀ ∩ W₀ = {a, b}) (hinter₁ : U₁ ∩ W₁ = {c, d})
    (hab : a ≠ b) (hcd : c ≠ d)
    (hf : PolyhedralPLInCharts e f D₀) (hg : PolyhedralPLInCharts e g D₁)
    (hfi : InjOn f D₀) (hgi : InjOn g D₁)
    (himage : f '' W₀ = g '' W₁) (ha : f a = g c) (hb : f b = g d) :
    ∃ H : D₀ ≃ₜ D₁, H.IsFinitePL ∧
      (∀ x : W₀, f x = g (H ⟨x, hD₀.1 (Or.inr x.property)⟩)) ∧
      (∀ x : D₀, (x : E) ∈ U₀ ∪ W₀ ↔ (H x : F) ∈ U₁ ∪ W₁) ∧
      (∀ x : D₀, (x : E) ∈ U₀ ↔ (H x : F) ∈ U₁) ∧
      ∀ x : D₀, (x : E) ∈ W₀ ↔ (H x : F) ∈ W₁ := by
  have hW₀D : W₀ ⊆ D₀ := subset_union_right.trans hD₀.1
  have hW₁D : W₁ ⊆ D₁ := subset_union_right.trans hD₁.1
  have hfW : PolyhedralPLInCharts e f W₀ := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJW, _⟩, _⟩, _⟩ := hW₀
    exact hJW ▸ hf.restrict_finite J hJ (hJW.subset.trans hW₀D)
  have hgW : PolyhedralPLInCharts e g W₁ := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJW, _⟩, _⟩, _⟩ := hW₁
    exact hJW ▸ hg.restrict_finite J hJ (hJW.subset.trans hW₁D)
  obtain ⟨r, hr, hrv⟩ := exists_original_interval_identification he hW₀ hW₁ hfW hgW
    (hfi.mono hW₀D) (hgi.mono hW₁D) himage
  obtain ⟨u₀, hu₀, hu₀a, hu₀b⟩ := hU₀.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨w₀, hw₀, hw₀a, hw₀b⟩ := hW₀.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨u₁, hu₁, hu₁c, hu₁d⟩ := hU₁.exists_unitInterval_chart_with_endpoints hcd
  let w₁ := w₀.trans r
  have hw₁ : w₁.IsFinitePL := hw₀.trans hr
  have hw₁c : (w₁ 0 : F) = c := by
    apply hgi (hW₁D (w₁ 0).property) (hW₁D (hW₁.1 (by simp)))
    exact (hrv (w₀ 0)).symm.trans ((congrArg f hw₀a).trans ha)
  have hw₁d : (w₁ 1 : F) = d := by
    apply hgi (hW₁D (w₁ 1).property) (hW₁D (hW₁.1 (by simp)))
    exact (hrv (w₀ 1)).symm.trans ((congrArg f hw₀b).trans hb)
  obtain ⟨B, hB, hBu, hBw⟩ := exists_prescribed_two_interval_homeomorph hinter₀ hinter₁
    u₀ w₀ u₁ w₁ hu₀ hw₀ hu₁ hw₁ hu₀a hu₀b hw₀a hw₀b hu₁c hu₁d hw₁c hw₁d
  obtain ⟨H, hH, hHB, hHrim⟩ := hD₀.exists_extension hD₁ B hB
  have hHu (t : unitInterval) :
      (H ⟨u₀ t, hD₀.1 (Or.inl (u₀ t).property)⟩ : F) = u₁ t :=
    (congrArg Subtype.val (hHB ⟨u₀ t, Or.inl (u₀ t).property⟩)).trans (hBu t)
  have hHw (t : unitInterval) :
      (H ⟨w₀ t, hW₀D (w₀ t).property⟩ : F) = w₁ t :=
    (congrArg Subtype.val (hHB ⟨w₀ t, Or.inr (w₀ t).property⟩)).trans (hBw t)
  have hU (x : D₀) : (x : E) ∈ U₀ ↔ (H x : F) ∈ U₁ := by
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := u₀.surjective ⟨x, hx⟩
      have heq : (⟨u₀ t, hD₀.1 (Or.inl (u₀ t).property)⟩ : D₀) = x :=
        Subtype.ext (congrArg (fun z : U₀ ↦ (z : E)) ht)
      exact (heq ▸ hHu t).symm ▸ (u₁ t).property
    · intro hx
      obtain ⟨t, ht⟩ := u₁.surjective ⟨H x, hx⟩
      have heq := H.injective (Subtype.ext ((hHu t).trans (congrArg Subtype.val ht)))
      exact congrArg Subtype.val heq ▸ (u₀ t).property
  have hW (x : D₀) : (x : E) ∈ W₀ ↔ (H x : F) ∈ W₁ := by
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := w₀.surjective ⟨x, hx⟩
      have heq : (⟨w₀ t, hW₀D (w₀ t).property⟩ : D₀) = x :=
        Subtype.ext (congrArg (fun z : W₀ ↦ (z : E)) ht)
      exact (heq ▸ hHw t).symm ▸ (w₁ t).property
    · intro hx
      obtain ⟨t, ht⟩ := w₁.surjective ⟨H x, hx⟩
      have heq := H.injective (Subtype.ext ((hHw t).trans (congrArg Subtype.val ht)))
      exact congrArg Subtype.val heq ▸ (w₀ t).property
  refine ⟨H, hH, ?_, hHrim, hU, hW⟩
  intro x
  obtain ⟨t, rfl⟩ := w₀.surjective x
  rw [hHw t]
  exact hrv (w₀ t)

end PoincareConjecture.M76.Dehn.Annuli
