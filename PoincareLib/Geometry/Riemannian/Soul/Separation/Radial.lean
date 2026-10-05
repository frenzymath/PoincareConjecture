import PoincareLib.Geometry.Riemannian.Soul.Separation.Spheres
import PoincareLib.Geometry.Riemannian.Distance.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Radial annuli and distance-sphere separation

The actual distance-parametrized radial homeomorphism gives connected radial
annuli and exteriors and compact closed annuli. Every connected set avoiding
a distance sphere lies entirely on one side of it.

Reference: Morgan--Tian, Lemma 2.20 and Proposition 2.19, pp. 31--32.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

namespace PoincareMT.RiemannianMetric

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

/-- A preconnected set avoiding a distance sphere lies entirely inside it or
entirely outside it. This follows from continuity of intrinsic distance. -/
theorem subset_distance_lt_or_gt_of_isPreconnected
    [T3Space M] [PreconnectedSpace M]
    (g : RiemannianMetric 3 M) (p : M) {r : ℝ} {S : Set M}
    (hS : IsPreconnected S) (havoid : Disjoint S (distanceSphere g p r)) :
    S ⊆ {x | (g.edist p x).toReal < r} ∨
      S ⊆ {x | r < (g.edist p x).toReal} := by
  have hne : ∀ x ∈ S, (g.edist p x).toReal ≠ r := by
    intro x hx hxr
    exact Set.disjoint_left.mp havoid hx hxr
  exact (hS.mapsTo_Ioi_or_Iio (g.continuous_toReal_edist p).continuousOn hne).symm

namespace RadialHomeomorph

variable {g : RiemannianMetric 3 M} {p : M}

private instance : ConnectedSpace UnitTwoSphere := by
  apply isConnected_iff_connectedSpace.mp
  exact isConnected_sphere
    (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)

private theorem center_distance : (g.edist p p).toReal = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have he : g.edist p p = 0 := Manifold.riemannianEDist_self
  rw [he, ENNReal.toReal_zero]

/-- A set of strictly positive distance values is parametrized by the
corresponding product of the unit sphere with that set of radii. -/
theorem distance_preimage_eq_range (H : RadialHomeomorph g p)
    {S : Set ℝ} (hS : S ⊆ Ioi 0) :
    {x | (g.edist p x).toReal ∈ S} =
      Set.range (fun z : UnitTwoSphere × S =>
        (H.toHomeomorph (z.1, ⟨z.2, hS z.2.property⟩) : M)) := by
  ext x
  constructor
  · intro hx
    have hxp : x ≠ p := by
      intro heq
      subst x
      have hpos := hS hx
      simp only [mem_Ioi, center_distance, lt_self_iff_false] at hpos
    let z := H.toHomeomorph.symm ⟨x, hxp⟩
    have hz : (H.toHomeomorph z : M) = x :=
      congrArg Subtype.val (H.toHomeomorph.apply_symm_apply ⟨x, hxp⟩)
    have hrz : (z.2 : ℝ) = (g.edist p x).toReal := by
      rw [← H.distance_eq z, hz]
    refine ⟨(z.1, ⟨z.2, hrz ▸ hx⟩), ?_⟩
    exact hz
  · rintro ⟨z, rfl⟩
    change (g.edist p (H.toHomeomorph (z.1, ⟨z.2, hS z.2.property⟩) : M)).toReal ∈ S
    rw [H.distance_eq]
    exact z.2.property

private theorem continuous_radial_restriction (H : RadialHomeomorph g p)
    {S : Set ℝ} (hS : S ⊆ Ioi 0) :
    Continuous (fun z : UnitTwoSphere × S =>
      (H.toHomeomorph (z.1, ⟨z.2, hS z.2.property⟩) : M)) := by
  exact continuous_subtype_val.comp (H.toHomeomorph.continuous.comp
    (continuous_fst.prodMk (continuous_snd.subtype_val.subtype_mk _)))

/-- A connected set of positive radii gives a connected intrinsic radial set. -/
theorem isConnected_distance_preimage (H : RadialHomeomorph g p)
    {S : Set ℝ} (hS : S ⊆ Ioi 0) (hconn : IsConnected S) :
    IsConnected {x | (g.edist p x).toReal ∈ S} := by
  let : ConnectedSpace S := isConnected_iff_connectedSpace.mp hconn
  rw [H.distance_preimage_eq_range hS]
  exact isConnected_range (H.continuous_radial_restriction hS)

/-- A compact set of positive radii gives a compact intrinsic radial set. -/
theorem isCompact_distance_preimage (H : RadialHomeomorph g p)
    {S : Set ℝ} (hS : S ⊆ Ioi 0) (hcomp : IsCompact S) :
    IsCompact {x | (g.edist p x).toReal ∈ S} := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hcomp
  rw [H.distance_preimage_eq_range hS]
  exact isCompact_range (H.continuous_radial_restriction hS)

/-- Every nonempty closed annulus with positive inner radius is connected. -/
theorem isConnected_distanceAnnulus (H : RadialHomeomorph g p)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IsConnected (distanceAnnulus g p a b) := by
  exact H.isConnected_distance_preimage
    (S := Icc a b) (fun _ hx => ha.trans_le hx.1) (isConnected_Icc hab)

/-- Every closed annulus with positive inner radius is compact. -/
theorem isCompact_distanceAnnulus (H : RadialHomeomorph g p)
    {a b : ℝ} (ha : 0 < a) : IsCompact (distanceAnnulus g p a b) := by
  exact H.isCompact_distance_preimage
    (S := Icc a b) (fun _ hx => ha.trans_le hx.1) isCompact_Icc

/-- The exterior of every nonnegative distance level is connected. -/
theorem isConnected_distance_exterior (H : RadialHomeomorph g p)
    {r : ℝ} (hr : 0 ≤ r) : IsConnected {x | r < (g.edist p x).toReal} := by
  exact H.isConnected_distance_preimage
    (S := Ioi r) (fun _ hx => hr.trans_lt hx) isConnected_Ioi

/-- Every open annulus between distinct nonnegative radii is connected. -/
theorem isConnected_open_distanceAnnulus (H : RadialHomeomorph g p)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    IsConnected {x | a < (g.edist p x).toReal ∧ (g.edist p x).toReal < b} := by
  exact H.isConnected_distance_preimage
    (S := Ioo a b) (fun _ hx => ha.trans_lt hx.1) (isConnected_Ioo hab)

/-- The center is a limit of every punctured positive-radius distance ball. -/
theorem center_mem_closure_open_distanceAnnulus
    [T3Space M] [PreconnectedSpace M]
    (H : RadialHomeomorph g p) {r : ℝ} (hr : 0 < r) :
    p ∈ closure {x | 0 < (g.edist p x).toReal ∧ (g.edist p x).toReal < r} := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  apply mem_closure_iff.mpr
  intro U hU hpU
  obtain ⟨δ, hδ, hδU⟩ :=
    setOfPred_riemannianEDist_lt_subset_nhds (𝓡 3) (hU.mem_nhds hpU)
  have hδreal : 0 < (δ : ℝ) := by exact_mod_cast hδ
  let s : ℝ := min r (δ : ℝ) / 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hsr : s < r := by dsimp [s]; linarith [min_le_left r (δ : ℝ)]
  have hsδ : s < (δ : ℝ) := by dsimp [s]; linarith [min_le_right r (δ : ℝ)]
  obtain ⟨q⟩ := (inferInstance : Nonempty UnitTwoSphere)
  let y : M := H.toHomeomorph (q, ⟨s, hs⟩)
  have hdy : (g.edist p y).toReal = s := H.distance_eq (q, ⟨s, hs⟩)
  refine ⟨y, ?_, ?_⟩
  · apply hδU
    change g.edist p y < (δ : ℝ≥0∞)
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top p y), hdy,
      ← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff hδreal).mpr hsδ
  · change 0 < (g.edist p y).toReal ∧ (g.edist p y).toReal < r
    rw [hdy]
    exact ⟨hs, hsr⟩

/-- Every positive-radius distance ball is connected, including its center. -/
theorem isConnected_distance_interior
    [T3Space M] [PreconnectedSpace M]
    (H : RadialHomeomorph g p) {r : ℝ} (hr : 0 < r) :
    IsConnected {x | (g.edist p x).toReal < r} := by
  apply (H.isConnected_open_distanceAnnulus le_rfl hr).subset_closure
    (fun _ hx => hx.2)
  intro x hx
  by_cases hxp : x = p
  · subst x
    exact H.center_mem_closure_open_distanceAnnulus hr
  · apply subset_closure
    refine ⟨?_, hx⟩
    let z := H.toHomeomorph.symm ⟨x, hxp⟩
    have hz : (H.toHomeomorph z : M) = x :=
      congrArg Subtype.val (H.toHomeomorph.apply_symm_apply ⟨x, hxp⟩)
    rw [← hz, H.distance_eq]
    exact z.2.property

/-- A positive distance sphere has two disjoint nonempty connected open
sides, the intrinsic interior and exterior, whose union is its complement. -/
theorem distanceSphere_compl_separation
    [T3Space M] [PreconnectedSpace M]
    (H : RadialHomeomorph g p) {r : ℝ} (hr : 0 < r) :
    IsOpen {x | (g.edist p x).toReal < r} ∧
      IsOpen {x | r < (g.edist p x).toReal} ∧
      IsConnected {x | (g.edist p x).toReal < r} ∧
      IsConnected {x | r < (g.edist p x).toReal} ∧
      Disjoint {x | (g.edist p x).toReal < r} {x | r < (g.edist p x).toReal} ∧
      (distanceSphere g p r)ᶜ =
        {x | (g.edist p x).toReal < r} ∪ {x | r < (g.edist p x).toReal} := by
  refine ⟨isOpen_lt (g.continuous_toReal_edist p) continuous_const,
    isOpen_lt continuous_const (g.continuous_toReal_edist p),
    H.isConnected_distance_interior hr, H.isConnected_distance_exterior hr.le,
    Set.disjoint_left.mpr (fun x (hx : (g.edist p x).toReal < r)
      (hy : r < (g.edist p x).toReal) => (lt_trans hx hy).false), ?_⟩
  ext x
  change (g.edist p x).toReal ≠ r ↔
    (g.edist p x).toReal < r ∨ r < (g.edist p x).toReal
  exact ne_iff_lt_or_gt

end RadialHomeomorph
end PoincareMT.RiemannianMetric
