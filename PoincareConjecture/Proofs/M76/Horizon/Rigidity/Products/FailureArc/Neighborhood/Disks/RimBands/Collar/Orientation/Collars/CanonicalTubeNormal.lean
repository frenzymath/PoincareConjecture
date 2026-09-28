import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Orientation.Collars.CollarNormalLabel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.TubeNormal

set_option autoImplicit false

open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)

def canonicalTubeBase : Set P2 := Ioo (-1 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1

def canonicalTubeCoordinates (side : Bool) (z : P2 × ℝ) : C3 :=
  ((z.1.1, if side then -(z.1.1 + z.2) else z.1.1 + z.2), z.1.2)

theorem continuous_canonicalTubeCoordinates (side : Bool) :
    Continuous (canonicalTubeCoordinates side) := by
  have hx : Continuous (fun z : P2 × ℝ => z.1.1) := continuous_fst.comp continuous_fst
  have ht : Continuous (fun z : P2 × ℝ => z.1.2) := continuous_snd.comp continuous_fst
  cases side
  · exact (hx.prodMk (hx.add continuous_snd)).prodMk ht
  · exact (hx.prodMk (hx.add continuous_snd).neg).prodMk ht

theorem tubeNormal_canonicalTubeCoordinates (side : Bool) (z : P2 × ℝ) :
    tubeNormal side (canonicalTubeCoordinates side z) = z.2 := by
  cases side <;> simp [tubeNormal, canonicalTubeCoordinates]

def canonicalTubeDomain (side : Bool) : Set (canonicalTubeBase × ℝ) :=
  (fun z => canonicalTubeCoordinates side (z.1, z.2)) ⁻¹' interior tube

theorem isOpen_canonicalTubeDomain (side : Bool) : IsOpen (canonicalTubeDomain side) :=
  isOpen_interior.preimage ((continuous_canonicalTubeCoordinates side).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd))

theorem canonicalTubeDomain_zero (side : Bool) (p : canonicalTubeBase) :
    (p, (0 : ℝ)) ∈ canonicalTubeDomain side := by
  change canonicalTubeCoordinates side (p.val, 0) ∈ interior tube
  simp only [tube, interior_prod_eq, interior_Icc]
  cases side
  · simpa only [canonicalTubeCoordinates, Bool.false_eq_true, if_false, add_zero] using
      (show ((p.val.1, p.val.1), p.val.2) ∈
        (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1 from
        ⟨⟨p.property.1, p.property.1⟩, p.property.2⟩)
  · simp only [canonicalTubeCoordinates, if_true, add_zero]
    change ((p.val.1, -p.val.1), p.val.2) ∈
      (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ×ˢ Ioo (0 : ℝ) 1
    exact ⟨⟨p.property.1, by constructor <;> linarith [p.property.1.1, p.property.1.2]⟩,
      p.property.2⟩

theorem isPreconnected_canonicalTubeBase : IsPreconnected canonicalTubeBase :=
  ((convex_Ioo (-1 : ℝ) 1).prod (convex_Ioo (0 : ℝ) 1)).isPreconnected

theorem nonempty_canonicalTubeBase : canonicalTubeBase.Nonempty :=
  ⟨(0, 1 / 2), by norm_num [canonicalTubeBase]⟩

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R W : Set X}
  {S T C D : Set P2} {f₀ f₁ : P2 → X}

def canonicalTubeCollar (U : OriginalIntervalTube e R W S T C D f₀ f₁)
    (side : Bool) (z : canonicalTubeBase × ℝ) : X :=
  U.map (canonicalTubeCoordinates side (z.1, z.2))

theorem continuousOn_canonicalTubeCollar
    (U : OriginalIntervalTube e R W S T C D f₀ f₁) (side : Bool) :
    ContinuousOn (canonicalTubeCollar U side) (canonicalTubeDomain side) :=
  U.pl.continuousOn.comp
    (((continuous_canonicalTubeCoordinates side).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).continuousOn)
    (fun _ hz => interior_subset hz)

theorem canonicalTubeCollar_surface_iff
    (U : OriginalIntervalTube e R W S T C D f₀ f₁) (side : Bool)
    (z : canonicalTubeBase × ℝ) (hz : z ∈ canonicalTubeDomain side) :
    canonicalTubeCollar U side z ∈
      (if side then f₁ '' T else f₀ '' S) \ frontier R ↔ z.2 = 0 := by
  have hzt : canonicalTubeCoordinates side (z.1, z.2) ∈ tube := interior_subset hz
  have hnot : canonicalTubeCollar U side z ∉ frontier R := by
    rw [canonicalTubeCollar, U.frontier_iff _ hzt]
    exact not_or.mpr ⟨ne_of_gt z.1.property.2.1, ne_of_lt z.1.property.2.2⟩
  simp only [mem_sdiff, hnot, not_false_eq_true, and_true]
  change U.map (canonicalTubeCoordinates side (z.1, z.2)) ∈
    (if side then f₁ '' T else f₀ '' S) ↔ z.2 = 0
  cases side
  · change U.map (canonicalTubeCoordinates false (z.1, z.2)) ∈ f₀ '' S ↔ z.2 = 0
    rw [U.first_trace _ hzt]
    change z.1.val.1 + z.2 = z.1.val.1 ↔ z.2 = 0
    simp
  · change U.map (canonicalTubeCoordinates true (z.1, z.2)) ∈ f₁ '' T ↔ z.2 = 0
    rw [U.second_trace _ hzt]
    change -(z.1.val.1 + z.2) = -z.1.val.1 ↔ z.2 = 0
    simp

theorem exists_constant_canonicalTube_normal_label
    {κ : Type*} (U : OriginalIntervalTube e R W S T C D f₀ f₁) (side : Bool)
    (E : κ → OpenPartialHomeomorph X C3)
    (hcover : ∀ x ∈ (if side then f₁ '' T else f₀ '' S) \ frontier R,
      ∃ i, x ∈ (E i).source)
    (hpair : ∀ i y, y ∈ (E i).source →
      (y ∈ (if side then f₁ '' T else f₀ '' S) \ frontier R ↔ (E i y).2 = 0))
    (hcompat : ∀ i j (x : ((if side then f₁ '' T else f₀ '' S) \ frontier R : Set X)),
      (x : X) ∈ (E i).source ∩ (E j).source →
        ∃ V : Set X, IsOpen V ∧ (x : X) ∈ V ∧
          EqOn (fun y => SignType.sign (E i y).2) (fun y => SignType.sign (E j y).2) V) :
    ∃ μ : SignType, μ ≠ 0 ∧ ∀ p : canonicalTubeBase,
      PositiveCollarSignAt E (canonicalTubeCollar U side) p μ := by
  obtain ⟨ν, hν, hn, hgerm⟩ := exists_collar_positive_normal_label
    (isOpen_canonicalTubeDomain side) (canonicalTubeCollar U side)
    (continuousOn_canonicalTubeCollar U side) (canonicalTubeDomain_zero side)
    (canonicalTubeCollar_surface_iff U side) E hcover hpair hcompat
  let : PreconnectedSpace canonicalTubeBase :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_canonicalTubeBase
  let p : canonicalTubeBase := ⟨(0, 1 / 2), by norm_num [canonicalTubeBase]⟩
  exact ⟨ν p, hn p, fun q => (hν.apply_eq_of_preconnectedSpace q p) ▸ hgerm q⟩

end PoincareConjecture.M76.Dehn.Annuli.RimBands
