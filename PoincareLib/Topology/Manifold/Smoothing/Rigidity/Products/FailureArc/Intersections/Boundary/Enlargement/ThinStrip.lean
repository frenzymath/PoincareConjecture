import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Boundary.Enlargement.Rectangle
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Arcs.Mathlib.CompactClosedStrip

/-! # Arbitrarily narrow proper strips about a returning arc -/

set_option autoImplicit false
open Set Geometry

namespace PoincareMT.M76.Dehn.Annuli

open PolygonalCrossingResolution
local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem exists_thin_proper_arc_strip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {T Q W O : Set E} {a b : E}
    (hT : IsFinitePLBallPair P2 T Q) (hW : IsFinitePLBallPair ℝ W {a, b})
    (hab : a ≠ b) (ha : a ∈ Q) (hb : b ∈ Q)
    (hproper : W \ {a, b} ⊆ T \ Q) (hO : IsOpen O) (hWO : W ⊆ O) :
    ∃ c : P2 → E, FinitePiecewiseAffineOn c source ∧ InjOn c source ∧
      MapsTo c source T ∧ MapsTo c source O ∧ c '' arm 0 = W ∧
      c (0, 0) = a ∧ c (1, 0) = b ∧
      (∀ x ∈ source, c x ∈ W ↔ x.2 = 0) ∧
      ∀ x ∈ source, c x ∈ Q ↔ x.1 = 0 ∨ x.1 = 1 := by
  obtain ⟨H, w, hH, _, hw0, hw1, haxis, hWiff, hQiff⟩ :=
    exists_proper_arc_rectangle_chart hT hW hab ha hb hproper
  let f : I × Icc (-1 : ℝ) 1 → E := fun x ↦ H ⟨(x.1, x.2), x.1.property, x.2.property⟩
  have hf : Continuous f := continuous_subtype_val.comp (H.continuous.comp
    (((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _))
  obtain ⟨δ, hδ, hδhalf, hstrip⟩ := hf.exists_closed_strip_subset hO (fun t ↦ by
    change (H ⟨((t : ℝ), 0), _⟩ : E) ∈ O
    rw [haxis]
    exact hWO (w t).property)
  let L : P2 →ᴬ[ℝ] P2 := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap.prod
    (δ • (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap)
  have hLy (x : P2) (hx : x ∈ source) : |δ * x.2| ≤ δ := by
    rw [abs_mul, abs_of_pos hδ]
    exact mul_le_of_le_one_right hδ.le (abs_le.mpr hx.2)
  have hLsource : MapsTo L source source := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have h := abs_le.mp ((hLy x hx).trans (show δ ≤ 1 by linarith))
    exact h
  obtain ⟨v, hv, hHv⟩ := hH
  obtain ⟨K, hK, hKs, _⟩ := hv
  have hL : FinitePiecewiseAffineOn L source := ⟨K, hK, hKs, K.affineOnFaces_affine L⟩
  have hv' : FinitePiecewiseAffineOn v source := by
    exact ⟨K, hK, hKs, by assumption⟩
  let c := v ∘ L
  have hc (x : P2) (hx : x ∈ source) : c x = (H ⟨L x, hLsource hx⟩ : E) :=
    (hHv ⟨L x, hLsource hx⟩).symm
  have hcenter (t : I) : c ((t : ℝ), 0) = (w t : E) := by
    rw [hc _ ⟨t.property, by norm_num⟩]
    simpa [L] using haxis t
  refine ⟨c, hv'.comp hL hLsource, ?_, ?_, ?_, ?_, hcenter 0 |>.trans hw0,
    hcenter 1 |>.trans hw1, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [hc x hx, hc y hy] at hxy
    have h := congrArg Subtype.val (H.injective (Subtype.ext hxy))
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext h1 (mul_left_cancel₀ hδ.ne' h2)
  · intro x hx
    rw [hc x hx]
    exact (H ⟨L x, hLsource hx⟩).property
  · intro x hx
    rw [hc x hx]
    exact hstrip ⟨x.1, hx.1⟩ ⟨δ * x.2, (hLsource hx).2⟩ (hLy x hx)
  · ext y
    constructor
    · rintro ⟨x, ⟨hx, hy⟩, rfl⟩
      have hy' : x.2 = 0 := hy
      have heq : x = (x.1, 0) := Prod.ext rfl hy'
      rw [heq, hcenter ⟨x.1, hx⟩]
      exact (w ⟨x.1, hx⟩).property
    · intro hy
      obtain ⟨t, ht⟩ := w.surjective ⟨y, hy⟩
      exact ⟨((t : ℝ), 0), ⟨t.property, rfl⟩,
        (hcenter t).trans (congrArg Subtype.val ht)⟩
  · intro x hx
    rw [hc x hx, hWiff]
    change δ * x.2 = 0 ↔ x.2 = 0
    exact mul_eq_zero.trans (or_iff_right hδ.ne')
  · intro x hx
    rw [hc x hx, hQiff]
    change (x.1 ∈ ({0, 1} : Set ℝ) ∧ δ * x.2 ∈ Icc (-1 : ℝ) 1) ∨
      (x.1 ∈ I ∧ δ * x.2 ∈ ({-1, 1} : Set ℝ)) ↔ x.1 = 0 ∨ x.1 = 1
    have hn : δ * x.2 ∉ ({-1, 1} : Set ℝ) := by
      have h := abs_le.mp (hLy x hx)
      simp only [mem_insert_iff, mem_singleton_iff]
      rintro (he | he) <;> linarith
    have hmem : δ * x.2 ∈ Icc (-1 : ℝ) 1 := (hLsource hx).2
    simp only [mem_insert_iff, mem_singleton_iff, hmem, and_true,
      hn, and_false, or_false]

end PoincareMT.M76.Dehn.Annuli
