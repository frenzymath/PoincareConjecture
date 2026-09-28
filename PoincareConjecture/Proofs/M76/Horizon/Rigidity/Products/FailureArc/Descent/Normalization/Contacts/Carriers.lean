import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.Comparison

set_option autoImplicit false
open Set Geometry Topology

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K K₀ K₁ : SimplicialComplex ℝ V} {j jfinal : V → t.Carrier}
  {Q : OpenPartialHomeomorph t.Carrier E}
  {B : OpenPartialHomeomorph s.Carrier E} {J : SimplicialComplex ℝ E}
  {N : K.faces → Set t.Carrier} {R Fmark : Set M} {boundary : Bool}

namespace MarkedSurfaceMotionData

variable (m : MarkedSurfaceMotionData step K K₀ K₁ j Q B J N R Fmark boundary)

def comparisonOpen : Set E := interior m.support.space ∩ m.fixedSource.spaceᶜ

omit [FiniteDimensional ℝ V] in
theorem comparisonOpen_open : IsOpen m.comparisonOpen :=
  isOpen_interior.inter (m.fixedSource.isCompact_space_of_finite
    m.protected_finite).isClosed.isOpen_compl

theorem active_coordinate_mem_comparisonOpen
    (hK₀ : K₀ ≤ K) (hK₁ : K₁ ≤ K) (hji : InjOn j K.space)
    (heq : EqOn jfinal (m.ambient 1 ∘ j) K₁.space)
    {x : V} (hx : x ∈ K₁.space) (hxold : x ∉ K₀.space) (hxQ : j x ∈ Q.source) :
    Q (jfinal x) ∈ m.comparisonOpen := by
  have hsupport := m.active_supported x hx hxold
  have hcoord := m.coordinate_of_successor_agreement heq hx hxQ (interior_subset hsupport)
  refine ⟨?_, ?_⟩
  · rw [hcoord]
    have himage := (m.coordinates.map 1).image_interior m.support.space
    have himage' := himage.trans (congrArg interior (m.coordinates.carrier 1))
    exact himage'.subset (mem_image_of_mem _ hsupport)
  · intro hw
    have hfixed := m.coordinates.fixed_protected 1 _ hw
    have hsame := (m.coordinates.map 1).injective (hcoord.symm.trans hfixed.symm)
    rw [m.protected_space] at hw
    obtain ⟨⟨_, ⟨⟨y, hy, rfl⟩, hyQ⟩, hyval⟩, _⟩ := hw
    have hmapsame := Q.injOn hxQ hyQ (hsame.trans hyval.symm)
    have hxy := hji (SimplicialComplex.space_subset_of_le hK₁ hx)
      (SimplicialComplex.space_subset_of_le hK₀ hy) hmapsame
    exact hxold (hxy.symm ▸ hy)

theorem coordinate_of_final_support
    (heq : EqOn jfinal (m.ambient 1 ∘ j) K₁.space)
    {x : V} (hx : x ∈ K₁.space) (hxQ : j x ∈ Q.source)
    (hxfinal : Q (jfinal x) ∈ m.support.space) :
    Q (j x) ∈ m.support.space ∧
      Q (jfinal x) = m.coordinates.map 1 (Q (j x)) := by
  have hxC : Q (j x) ∈ m.support.space := by
    by_contra hn
    have hout : j x ∉ Q.symm '' m.support.space := by
      rintro ⟨z, hz, hzj⟩
      apply hn
      have hzQ := Q.right_inv (m.support_upper hz)
      rw [hzj] at hzQ
      exact hzQ.symm ▸ hz
    have hext := m.exterior 1 (x := j x) hout
    have hsame : jfinal x = j x := (heq hx).trans hext
    exact hn (hsame ▸ hxfinal)
  exact ⟨hxC, m.coordinate_of_successor_agreement heq hx hxQ hxC⟩

theorem active_carrier_iff
    {face : Finset V}
    (hsucc : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V))
    (heq : EqOn jfinal (m.ambient 1 ∘ j) K₁.space)
    (hQinitial : MapsTo j (convexHull ℝ (face : Set V)) Q.source)
    (hQfinal : MapsTo jfinal (convexHull ℝ (face : Set V)) Q.source)
    (hval : ∀ x, Q x = B (step.projection (step.inclusion x)))
    (hmaps : MapsTo (step.projection ∘ step.inclusion) Q.source B.source)
    {z : E} (hz : z ∈ m.comparisonOpen) :
    z ∈ m.coordinates.map 1 '' m.freeComplex.space ↔
      z ∈ B '' (((step.projection ∘ step.inclusion) ∘ jfinal) ''
        convexHull ℝ (face : Set V) ∩ B.source) := by
  rw [m.free_space]
  constructor
  · rintro ⟨w, hw, hwz⟩
    rw [m.source_space] at hw
    obtain ⟨⟨_, ⟨⟨q, hqnext, rfl⟩, hqQ⟩, hqw⟩, hwJ⟩ := hw
    have hqnot : q ∉ K₀.space := by
      intro hqold
      have hwfixed : w ∈ m.fixedSource.space := by
        rw [m.protected_space]
        exact ⟨⟨j q, ⟨mem_image_of_mem _ hqold, hqQ⟩, hqw⟩, hwJ⟩
      exact hz.2 ((m.coordinates.fixed_protected 1 w hwfixed).symm.trans hwz ▸ hwfixed)
    have hqface := (hsucc.subset hqnext).resolve_left hqnot
    have hqcoord : Q (jfinal q) = z :=
      (m.coordinate_of_successor_agreement heq hqnext hqQ (hqw.symm ▸ hwJ)).trans
        ((congrArg (m.coordinates.map 1) hqw).trans hwz)
    exact ⟨step.projection (step.inclusion (jfinal q)),
      ⟨mem_image_of_mem _ hqface, hmaps (hQfinal hqface)⟩,
      (hval (jfinal q)).symm.trans hqcoord⟩
  · rintro ⟨_, ⟨⟨q, hqface, rfl⟩, _⟩, hqz⟩
    have hqnext := hsucc.symm.subset (Or.inr hqface)
    have hcoord : Q (jfinal q) = z := (hval (jfinal q)).trans hqz
    obtain ⟨hsupport, hvalue⟩ := m.coordinate_of_final_support heq hqnext
      (hQinitial hqface) (hcoord.symm ▸ interior_subset hz.1)
    refine ⟨Q (j q), ?_, hvalue.symm.trans hcoord⟩
    rw [m.source_space]
    exact ⟨⟨j q, ⟨mem_image_of_mem _ hqnext, hQinitial hqface⟩, rfl⟩, hsupport⟩

theorem prior_carrier_iff
    (heq : EqOn jfinal j K₀.space) (old : K₀.faces)
    {z : E} (hz : z ∈ m.comparisonOpen) :
    z ∈ (m.targets old).space ↔
      z ∈ B '' (((step.projection ∘ step.inclusion) ∘ jfinal) ''
        convexHull ℝ (old.val : Set V) ∩ B.source) := by
  rw [m.targets_space_of_prefix_agreement heq old]
  exact and_iff_left (interior_subset hz.1)

end MarkedSurfaceMotionData
end Geometry.OriginalPLTower
