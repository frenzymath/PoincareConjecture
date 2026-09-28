import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.FreeFaces
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleInteriorCrossingChart

set_option autoImplicit false

open Set Metric Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {U V M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}

theorem MarkedSurfaceMotionData.exists_triangle_comparison_chart
    {s t : Stage e S f r C} {step : Step s t}
    {K K₀ K₁ : SimplicialComplex ℝ V} (hK : K.faces.Finite)
    (hcard : ∀ c ∈ K.faces, c.card ≤ 3) (hK₀ : K₀ ≤ K)
    {face : Finset V} (hface : face ∈ K.faces)
    (hsucc : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V))
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    {Q : OpenPartialHomeomorph t.Carrier V3}
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    {B : OpenPartialHomeomorph s.Carrier V3} {J : SimplicialComplex ℝ V3}
    {N : K.faces → Set t.Carrier} {R Fmark : Set M} {boundary : Bool}
    (m : MarkedSurfaceMotionData step K K₀ K₁ j Q B J N R Fmark boundary)
    (old : K₀.faces) {a b : Finset V3}
    (ha : a ∈ m.freeComplex.faces) (ha0 : a ∉ m.fixedComplex.faces)
    (hb : b ∈ (m.targets old).faces) (ha3 : a.card = 3) (hb3 : b.card = 3)
    (hspan : affineSpan ℝ (m.coordinates.map 1 '' (a : Set V3) ∪ (b : Set V3)) = ⊤)
    {p : V3} (hpa : p ∈ intrinsicInterior ℝ
      (convexHull ℝ (m.coordinates.map 1 '' (a : Set V3))))
    (hpb : p ∈ intrinsicInterior ℝ (convexHull ℝ (b : Set V3)))
    {O : Set V3} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ H : OpenPartialHomeomorph V3 C3,
      p ∈ H.source ∧ H.source ⊆ O ∧ H p = 0 ∧
      LocallyPiecewiseAffineOn H H.source ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ z ∈ H.source, z ∈ m.coordinates.map 1 '' m.freeComplex.space ↔ (H z).2 = 0) ∧
      ∀ z ∈ H.source, z ∈ (m.targets old).space ↔ (H z).1.1 = 0 := by
  classical
  let F := m.coordinates.map 1
  have hF : m.freeComplex.AffineOnFaces F := fun c hc => m.endpoint_affine c (m.free_le hc)
  let A := hF.embeddedImage F.injective.injOn
  have hAf : A.faces.Finite := hF.embeddedImage_finite F.injective.injOn
    (m.subdivision_finite.subset m.free_le)
  have hAs : A.space = F '' m.freeComplex.space := hF.embeddedImage_space F.injective.injOn
  have hAa : a.image F ∈ A.faces := by
    rw [hF.embeddedImage_faces F.injective.injOn]
    exact ⟨a, ha, rfl⟩
  have hAcard : (a.image F).card = 3 := (Finset.card_image_of_injective _ F.injective).trans ha3
  obtain ⟨_, _, _, _, hfree⟩ := m.exists_active_face_bound hK hface hsucc hj hQ
  have hmaxA : ∀ c ∈ A.faces, a.image F ⊆ c → c = a.image F := by
    intro c hc hac
    rw [hF.embeddedImage_faces F.injective.injOn] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    have had : a ⊆ d := (Finset.image_subset_image_iff F.injective).mp hac
    have hd0 : d ∉ m.fixedComplex.faces := by
      intro hd0
      exact ha0 (m.fixedComplex.down_closed hd0 had (m.freeComplex.nonempty_of_mem_faces ha))
    have hd3 := (hfree d hd hd0).2.trans (hcard _ hface)
    have heq : a = d := Finset.eq_of_subset_of_card_le had (by omega)
    exact congrArg (fun d : Finset V3 => d.image F) heq.symm
  have hmaxB : ∀ c ∈ (m.targets old).faces, b ⊆ c → c = b := by
    intro c hc hbc
    have hc3 := (m.targets_card old c hc).trans (hcard _ (hK₀ old.property))
    exact (Finset.eq_of_subset_of_card_le hbc (by omega)).symm
  have hspan' : affineSpan ℝ ((a.image F : Set V3) ∪ (b : Set V3)) = ⊤ := by
    simpa only [Finset.coe_image] using hspan
  have hpa' : p ∈ intrinsicInterior ℝ (convexHull ℝ (a.image F : Set V3)) := by
    simpa only [Finset.coe_image] using hpa
  obtain ⟨H, hpH, hHO, hH0, hH, hHi, hHA, hHB⟩ :=
    A.exists_triangle_interior_crossing_chart (by simp) (m.targets old)
      hAf (m.targets_finite old) hAa hb hAcard hb3 hmaxA hmaxB hspan' hpa' hpb hO hpO
  refine ⟨H, hpH, hHO, hH0, hH, hHi, ?_, hHB⟩
  intro z hz
  rw [← hAs]
  exact hHA z hz

end Geometry.OriginalPLTower
