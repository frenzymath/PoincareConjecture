import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Construction

set_option autoImplicit false
open Set Metric Geometry Topology unitInterval PLAnnularStrip

namespace Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Rim" => Set.ofPred (fun z : P2 => depth 8 z = -1 ∨ depth 8 z = 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M} {s t : Stage e S f r C}
  {step : Step s t} {j : P2 → t.Carrier} {R Fmark : Set M}
  {a b : Ann} {W : Set s.Carrier} {ε : ℝ}
  (A : PlanarAnnulusBoundaryMotion step j R Fmark a b W ε)

theorem support_right_target : A.support.space ⊆ (A.window.right.trans A.chart).target := by
  intro z hz
  have hzQ := A.support_target hz
  exact ⟨hzQ, A.window.right_target.symm.subset
    (A.chart_inside (A.chart.map_target hzQ)).2⟩

theorem ambient_mem_right_source_iff (u : I) (x : t.Carrier) :
    A.ambient u x ∈ (A.window.right.trans A.chart).source ↔
      x ∈ (A.window.right.trans A.chart).source := by
  let T := A.window.right.trans A.chart
  have hout (y : t.Carrier) (hy : y ∉ T.source) : A.ambient u y = y := by
    apply A.outside u
    rintro ⟨z, hz, rfl⟩
    exact hy (T.map_target (A.support_right_target hz))
  constructor
  · intro hx
    by_contra hn
    exact hn (hout x hn ▸ hx)
  · intro hx
    by_contra hn
    have hfix := hout (A.ambient u x) hn
    have heq : A.ambient u x = x := (A.ambient u).injective hfix
    exact hn (heq.symm ▸ hx)

theorem ambient_right_coordinate (u : I) (x : t.Carrier)
    (hx : x ∈ (A.window.right.trans A.chart).source) :
    (A.window.right.trans A.chart) (A.ambient u x) =
      A.motion.map u ((A.window.right.trans A.chart) x) := by
  let T := A.window.right.trans A.chart
  rw [A.formula u hx]
  change T (T.symm (A.motion.map u (T x))) = A.motion.map u (T x)
  apply T.right_inv
  by_cases hz : T x ∈ A.support.space
  · exact A.support_right_target
      ((A.motion.carrier u).subset (mem_image_of_mem (A.motion.map u) hz))
  · rw [A.motion.outside u (T x) (fun h => hz (interior_subset h))]
    exact T.map_source hx

theorem clipped_image (u : I) (D : Set P2) :
    (A.window.right.trans A.chart) ''
        (((A.ambient u) ∘ j) '' D ∩ (A.window.right.trans A.chart).source) ∩
      A.support.space =
    A.motion.map u '' ((A.window.right.trans A.chart) ''
      (j '' D ∩ (A.window.right.trans A.chart).source) ∩ A.support.space) := by
  let T := A.window.right.trans A.chart
  have hJiff (z : V3) : A.motion.map u z ∈ A.support.space ↔ z ∈ A.support.space := by
    constructor
    · intro hz
      obtain ⟨y, hy, heq⟩ := (A.motion.carrier u).symm.subset hz
      exact (A.motion.map u).injective heq ▸ hy
    · intro hz
      exact (A.motion.carrier u).subset (mem_image_of_mem (A.motion.map u) hz)
  apply Subset.antisymm
  · rintro z ⟨⟨y, ⟨⟨x, hx, hxy⟩, hyT⟩, hyz⟩, hzJ⟩
    have hxy' : A.ambient u (j x) = y := hxy
    have hxT : j x ∈ T.source :=
      (A.ambient_mem_right_source_iff u _).mp (hxy'.symm ▸ hyT)
    have heq : A.motion.map u (T (j x)) = z :=
      (A.ambient_right_coordinate u _ hxT).symm.trans ((congrArg T hxy).trans hyz)
    exact ⟨T (j x), ⟨⟨j x, ⟨mem_image_of_mem j hx, hxT⟩, rfl⟩,
      (hJiff _).mp (heq.symm ▸ hzJ)⟩, heq⟩
  · rintro z ⟨y, ⟨⟨v, ⟨⟨x, hx, hxv⟩, hvT⟩, hvy⟩, hyJ⟩, rfl⟩
    have hxT : j x ∈ T.source := hxv.symm ▸ hvT
    have hxy : T (j x) = y := (congrArg T hxv).trans hvy
    refine ⟨⟨A.ambient u (j x), ⟨⟨x, hx, rfl⟩,
      (A.ambient_mem_right_source_iff u _).mpr hxT⟩, ?_⟩, (hJiff _).mpr hyJ⟩
    rw [A.ambient_right_coordinate u _ hxT, hxy]

theorem source_image (u : I) :
    (A.window.right.trans A.chart) ''
        (((A.ambient u) ∘ j) '' Ann ∩ (A.window.right.trans A.chart).source) ∩
      A.support.space = A.motion.map u '' A.source.space := by
  rw [A.clipped_image, A.source_space]

theorem boundary_image (u : I) :
    (A.window.right.trans A.chart) ''
        (((A.ambient u) ∘ j) '' Rim ∩ (A.window.right.trans A.chart).source) ∩
      A.support.space = A.motion.map u '' A.boundary.space := by
  rw [A.clipped_image, A.boundary_space]

end Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion
