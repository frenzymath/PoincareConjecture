import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Arcs.SquareAnnularStrips

/-!
# Actual rotated charts of the square annulus

The four mitered bands are affine quarter-turn images of the
same constructed finite PL strip. Each chart retains its
literal formula for the later cyclic endpoint gluing. See
Hatcher's punctured-torus picture, p. 7, Hamilton 1976, p. 66,
and M76 derivation 270.
-/

set_option autoImplicit false

open Set Geometry

namespace PLAnnularStrip

/-- The four exact quarter-turn affine maps about the square
center. See Hatcher p. 7 and M76 derivation 270. -/
noncomputable def stripRotation (L : ℝ) : Fin 4 → (ℝ × ℝ) →ᴬ[ℝ] (ℝ × ℝ) :=
  let x := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  let y := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  let c := ContinuousAffineMap.const ℝ (ℝ × ℝ) L
  ![x.prod y, (c - y).prod x, (c - x).prod (c - y), y.prod (c - x)]

/-- The actual target of each quarter-turn strip chart. See
Hatcher p. 7 and M76 derivation 270. -/
def stripRegion (L d : ℝ) : Fin 4 → Set (ℝ × ℝ) :=
  ![trapezoid L d, rightStrip L d, topStrip L d, leftStrip L d]

/-- Every quarter-turn map is injective on the entire plane.
See M76 derivation 270. -/
theorem stripRotation_injective (L : ℝ) (i : Fin 4) :
    Function.Injective (stripRotation L i) := by
  fin_cases i <;> intro p q hpq
  all_goals
    have h₁ := congrArg Prod.fst hpq
    have h₂ := congrArg Prod.snd hpq
    dsimp [stripRotation] at h₁ h₂
    exact Prod.ext (by linarith) (by linarith)

/-- Rotating the whole basic trapezoid gives exactly its
declared annulus strip, including its miter edges. See
M76 derivation 270. -/
theorem stripRotation_image (L d : ℝ) (i : Fin 4) :
    stripRotation L i '' trapezoid L d = stripRegion L d i := by
  fin_cases i
  · change (fun p : ℝ × ℝ => (p.1, p.2)) '' trapezoid L d = trapezoid L d
    exact image_id _
  · ext p
    change p ∈ (fun q : ℝ × ℝ => (L - q.2, q.1)) '' trapezoid L d ↔
      p ∈ rightStrip L d
    constructor
    · rintro ⟨q, ⟨ht, hx⟩, rfl⟩
      change L - (L - q.2) ∈ Icc (-d) d ∧ q.1 ∈ Icc (L - (L - q.2)) (L - q.2)
      simpa only [sub_sub_cancel] using And.intro ht hx
    · rintro ⟨ht, hx⟩
      refine ⟨(p.2, L - p.1), ⟨ht, ?_⟩, Prod.ext ?_ rfl⟩
      · change p.2 ∈ Icc (L - p.1) (L - (L - p.1))
        simpa only [sub_sub_cancel] using hx
      · ring
  · ext p
    change p ∈ (fun q : ℝ × ℝ => (L - q.1, L - q.2)) '' trapezoid L d ↔
      p ∈ topStrip L d
    constructor
    · rintro ⟨q, ⟨ht, hx⟩, rfl⟩
      change L - (L - q.2) ∈ Icc (-d) d ∧
        L - q.1 ∈ Icc (L - (L - q.2)) (L - q.2)
      refine ⟨by simpa only [sub_sub_cancel] using ht, ?_⟩
      constructor <;> linarith [hx.1, hx.2]
    · rintro ⟨ht, hx⟩
      refine ⟨(L - p.1, L - p.2), ⟨ht, ?_⟩, Prod.ext ?_ ?_⟩
      · change L - p.1 ∈ Icc (L - p.2) (L - (L - p.2))
        constructor <;> linarith [hx.1, hx.2]
      · ring
      · ring
  · ext p
    change p ∈ (fun q : ℝ × ℝ => (q.2, L - q.1)) '' trapezoid L d ↔
      p ∈ leftStrip L d
    constructor
    · rintro ⟨q, ⟨ht, hx⟩, rfl⟩
      change q.2 ∈ Icc (-d) d ∧ L - q.1 ∈ Icc q.2 (L - q.2)
      exact ⟨ht, by constructor <;> linarith [hx.1, hx.2]⟩
    · rintro ⟨ht, hx⟩
      refine ⟨(L - p.2, p.1), ⟨ht, ?_⟩, Prod.ext rfl ?_⟩
      · change L - p.2 ∈ Icc p.1 (L - p.1)
        constructor <;> linarith [hx.1, hx.2]
      · ring

/-- All four annular bands have actual finite PL rectangle
charts with their exact rotated coordinate maps retained.
No quotient or global injectivity is assumed. See Hatcher
p. 7, Hamilton p. 66 and M76 derivation 270. -/
theorem exists_rotated_strip_charts {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) :
    ∀ i : Fin 4, ∃ e : rectangle L d ≃ₜ stripRegion L d i,
      e.IsFinitePL ∧ ∀ p : rectangle L d,
        (e p : ℝ × ℝ) = stripRotation L i (stripMap L p) := by
  obtain ⟨e₀, he₀, he₀val⟩ := exists_finitePL_strip_homeomorph hd hwidth
  obtain ⟨f, hf, hfval⟩ := he₀
  have hPL : FinitePiecewiseAffineOn (stripMap L) (rectangle L d) :=
    hf.congr fun p hp => (hfval ⟨p, hp⟩).symm.trans (he₀val ⟨p, hp⟩)
  intro i
  have hrot := hPL.postcomp (stripRotation L i)
  have hinj : InjOn ((stripRotation L i) ∘ stripMap L) (rectangle L d) := by
    intro p hp q hq he
    exact stripMap_injOn hwidth hp hq ((stripRotation_injective L i) he)
  have himage : ((stripRotation L i) ∘ stripMap L) '' rectangle L d = stripRegion L d i := by
    rw [image_comp, stripMap_image hwidth, stripRotation_image]
  have he := hrot.exists_homeomorph_image hinj
  rw [himage] at he
  exact he

end PLAnnularStrip
