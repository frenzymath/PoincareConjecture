import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonFinitePLImage
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.FinitePLHomeomorph

/-!
# Transporting the actual polygons in a finite PL level comparison

Every polygon retains its index under a finite PL homeomorphism.
Finite subdivision supplies actual target polygons, and injectivity
retains their incidence in the distinguished residue. See Alexander
1924, pp. 6--8, Hudson pp. 15--16 and M76 derivation 246.
-/

set_option autoImplicit false

open Set Geometry

namespace Polygon

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite PL level comparison transports every original polygon
to a simple polygon with the same index. Coverage and pairwise
incidence in the residue are exact, including empty families.
See Alexander pp. 6--8 and derivation 246. -/
theorem exists_finitePL_image_family (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hPe : ∀ i, (P i).HasSimplicialEdges) (hPi : ∀ i, Function.Injective (P i))
    {s r : Set E} {t : Set F} (hcover : s = r ∪ ⋃ i, (P i).boundary ℝ)
    (hpair : Pairwise (fun i j => (P i).boundary ℝ ∩ (P j).boundary ℝ ⊆ r))
    (e : s ≃ₜ t) (he : e.IsFinitePL) :
    ∃ (f : E → F) (N : ι → ℕ) (Q : ∀ i, Polygon F (N i + 3)),
      FinitePiecewiseAffineOn f s ∧ (∀ x : s, (e x : F) = f x) ∧
      (∀ i, Function.Injective (Q i) ∧ (Q i).HasSimplicialEdges ∧
        (Q i).boundary ℝ = f '' (P i).boundary ℝ) ∧
      t = f '' r ∪ ⋃ i, (Q i).boundary ℝ ∧
      Pairwise (fun i j => (Q i).boundary ℝ ∩ (Q j).boundary ℝ ⊆ f '' r) := by
  classical
  obtain ⟨f, hf, hef⟩ := he
  have hPsub (i : ι) : (P i).boundary ℝ ⊆ s := by
    intro x hx
    rw [hcover]
    exact Or.inr (mem_iUnion.mpr ⟨i, hx⟩)
  have hfi : InjOn f s := by
    intro x hx y hy hxy
    have hexy : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [hef] using hxy
    exact congrArg Subtype.val (e.injective hexy)
  have himage : f '' s = t := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hef, e.apply_symm_apply]
  have hpolygons (i : ι) := (P i).exists_polygon_finitePL_image (hPe i) (hPi i)
    hf (hPsub i) (hfi.mono (hPsub i))
  choose N Q hQi hQe hQb using hpolygons
  refine ⟨f, N, Q, hf, hef, fun i => ⟨hQi i, hQe i, hQb i⟩, ?_, ?_⟩
  · rw [← himage, hcover, image_union, image_iUnion]
    simp only [hQb]
  · intro i j hij y hy
    rw [hQb i, hQb j] at hy
    obtain ⟨x, hxi, hxy⟩ := hy.1
    obtain ⟨z, hzj, hzy⟩ := hy.2
    have hxz : x = z := hfi (hPsub i hxi) (hPsub j hzj) (hxy.trans hzy.symm)
    exact ⟨x, hpair hij ⟨hxi, hxz.symm ▸ hzj⟩, hxy⟩

end Polygon
