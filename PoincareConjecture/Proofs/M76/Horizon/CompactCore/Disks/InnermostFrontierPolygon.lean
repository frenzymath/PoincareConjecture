import PoincareConjecture.Proofs.M76.Mathlib.InnermostPolygonDisk
import PoincareConjecture.Proofs.M76.Mathlib.PolygonAffineImage
import PoincareConjecture.Proofs.M76.Mathlib.PolygonConvexContainment
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Collars.PolygonTransportedExteriorCollar









set_option autoImplicit false

open Set Metric Geometry unitInterval

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1




theorem exists_innermost_frontier_polygon_disk_with_collar
    {S : Set (Set V2)} (hS : S.Finite) (hne : S.Nonempty)
    (hpoly : ∀ s ∈ S, ∃ n : ℕ, ∃ p : Polygon V2 (n + 3),
      Function.Injective p ∧ p.HasSimplicialEdges ∧ p.boundary ℝ = s)
    (hdisj : S.PairwiseDisjoint id) (hsub : ∀ s ∈ S, s ⊆ interior D) :
    ∃ (s : Set V2) (B : Set V2) (a : D ≃ₜ B) (d : V2 → V2),
      s ∈ S ∧ IsFinitePLBallPair (ℝ × ℝ) B s ∧ B ⊆ interior D ∧
      frontier B = s ∧ a.IsFinitePL ∧ FinitePiecewiseAffineOn d D ∧
      (∀ x : D, d x = (a x : V2)) ∧
      Topology.IsEmbedding (fun x : D => d x.val) ∧ d '' D = B ∧
      d '' frontier D = s ∧ (∀ x : D, d x ∈ s ↔ (x : V2) ∈ frontier D) ∧
      B ∩ (⋃ t ∈ S, t) = s ∧ Disjoint (interior B) (⋃ t ∈ S, t) ∧
      ∀ W : Set V2, IsOpen W → s ⊆ W →
        ∃ k : C(s × I, V2), Topology.IsEmbedding k ∧
          (∀ z : s, k (z, 0) = z) ∧ (∀ z, k z ∈ W) ∧
          (∀ (z : s) (t : I), 0 < (t : ℝ) → k (z, t) ∉ B) ∧
          IsCompact (B ∪ range k) ∧ B ⊆ interior (B ∪ range k) ∧
          frontier (B ∪ range k) ⊆ range (fun z : s => k (z, 1)) := by
  classical
  let : Finite S := hS.to_subtype
  let : Nonempty S := hne.to_subtype
  choose n P hPi hPe hPb using fun s : S => hpoly s s.property
  let c : V2 ≃L[ℝ] (ℝ × ℝ) := ContinuousLinearEquiv.ofFinrankEq (by
    simp [Module.finrank_prod])
  let R (i : S) : Polygon (ℝ × ℝ) (n i + 3) :=
    (P i).affineImage c.toLinearEquiv.toAffineEquiv.toAffineMap
  have hRi (i : S) : Function.Injective (R i) := c.injective.comp (hPi i)
  have hRe (i : S) : (R i).HasSimplicialEdges :=
    (P i).hasSimplicialEdges_affineImage (hPe i) _ c.injective
  have hRb (i : S) : (R i).boundary ℝ = c '' (i : Set V2) := by
    change ((P i).affineImage _).boundary ℝ = _
    rw [Polygon.affineImage_boundary, hPb]
    rfl
  have hRd : Pairwise (fun i j : S =>
      Disjoint ((R i).boundary ℝ) ((R j).boundary ℝ)) := by
    intro i j hij
    rw [hRb, hRb]
    exact (hdisj i.property j.property (fun h => hij (Subtype.ext h))).image
      c.injective.injOn (subset_univ _) (subset_univ _)
  obtain ⟨i, hball, hinter, havoid⟩ :=
    Polygon.exists_innermost_finitePL_disk n R hRe hRi hRd
  let B : Set V2 := c.symm '' closure (R i).inside
  have hboundary : c.symm '' (R i).boundary ℝ = (i : Set V2) := by
    rw [hRb]
    simp only [image_image, c.symm_apply_apply, image_id']
  have hballB : IsFinitePLBallPair (ℝ × ℝ) B (i : Set V2) := by
    have h := hball.affine_image c.symm.toContinuousLinearMap.toContinuousAffineMap
      c.symm.injective.injOn
    exact hboundary ▸ h
  have hBfront : frontier B = (i : Set V2) := by
    rw [show B = c.symm.toHomeomorph '' closure (R i).inside from rfl,
      ← c.symm.toHomeomorph.image_frontier, (R i).frontier_closure_inside (hRe i) (hRi i)]
    exact hboundary
  have hBint : interior B = c.symm '' (R i).inside := by
    rw [show B = c.symm.toHomeomorph '' closure (R i).inside from rfl,
      ← c.symm.toHomeomorph.image_interior, (R i).interior_closure_inside (hRe i) (hRi i)]
    rfl
  have hBsub : B ⊆ interior D := by
    have hc : closure (R i).inside ⊆ c '' interior D :=
      (R i).closure_inside_subset_convex (hRe i) (hRi i)
        ((convex_closedBall (0 : V2) 1).interior.linear_image c.toLinearMap) (by
          rintro _ ⟨v, rfl⟩
          exact ⟨P i v, hsub i i.property (hPb i ▸
            mem_iUnion.mpr ⟨v, left_mem_affineSegment ℝ _ _⟩), rfl⟩)
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hc hx
    simpa only [c.symm_apply_apply] using hy
  have hfamily : (⋃ j : S, (R j).boundary ℝ) = c '' (⋃ t ∈ S, t) := by
    simp only [hRb, image_iUnion]
    exact iUnion_subtype _ _
  have hinterB : B ∩ (⋃ t ∈ S, t) = (i : Set V2) := by
    apply Subset.antisymm
    · rintro x ⟨⟨y, hy, hyx⟩, hx⟩
      have hcy : c x = y := by rw [← hyx, c.apply_symm_apply]
      have hmem : c x ∈ closure (R i).inside ∩ (⋃ j : S, (R j).boundary ℝ) :=
        ⟨hcy ▸ hy, hfamily ▸ mem_image_of_mem c hx⟩
      have hrim := hinter.subset hmem
      rw [hRb] at hrim
      exact c.injective.mem_set_image.mp hrim
    · intro x hx
      exact ⟨hballB.1 hx, mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨i.property, hx⟩⟩⟩
  have havoidB : Disjoint (interior B) (⋃ t ∈ S, t) := by
    apply Set.disjoint_left.mpr
    rintro x hx hs
    rw [hBint] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    apply Set.disjoint_left.mp havoid hy
    rw [hfamily]
    exact ⟨c.symm y, hs, c.apply_symm_apply y⟩
  obtain ⟨e, he, heb⟩ := hballB.exists_cube_chart c.symm
  let a : D ≃ₜ B := e.symm
  have ha : a.IsFinitePL := he.symm
  obtain ⟨d, hd, had⟩ := ha
  have hval (x : D) : d x = (a x : V2) := (had x).symm
  have hrim (x : D) : d x ∈ (i : Set V2) ↔ (x : V2) ∈ frontier D := by
    rw [hval]
    simpa only [a, e.apply_symm_apply] using heb (a x)
  have himage : d '' D = B := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hval ⟨x, hx⟩]
      exact (a ⟨x, hx⟩).property
    · intro hy
      refine ⟨a.symm ⟨y, hy⟩, (a.symm ⟨y, hy⟩).property, ?_⟩
      rw [hval, a.apply_symm_apply]
  have hrimimage : d '' frontier D = (i : Set V2) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hrim ⟨x, isClosed_closedBall.frontier_subset hx⟩).mpr hx
    · intro hy
      obtain ⟨x, hx, hxy⟩ := himage.superset (hballB.1 hy)
      exact ⟨x, (hrim ⟨x, hx⟩).mp (hxy ▸ hy), hxy⟩
  refine ⟨i, B, a, d, i.property, hballB, hBsub, hBfront, ⟨d, hd, had⟩,
    hd, hval, ?_, himage, hrimimage, hrim, hinterB, havoidB, ?_⟩
  · have hfun : (fun x : D => d x.val) = (Subtype.val : B → V2) ∘ a :=
      funext hval
    rw [hfun]
    exact Topology.IsEmbedding.subtypeVal.comp a.isEmbedding
  · intro W hW hiW
    exact (R i).exists_transported_closed_exterior_collar (hRe i) (hRi i)
      c.toHomeomorph (hRb i) rfl hW hiW

theorem exists_innermost_frontier_polygon_disk
    {S : Set (Set V2)} (hS : S.Finite) (hne : S.Nonempty)
    (hpoly : ∀ s ∈ S, ∃ n : ℕ, ∃ p : Polygon V2 (n + 3),
      Function.Injective p ∧ p.HasSimplicialEdges ∧ p.boundary ℝ = s)
    (hdisj : S.PairwiseDisjoint id) (hsub : ∀ s ∈ S, s ⊆ interior D) :
    ∃ (s : Set V2) (B : Set V2) (a : D ≃ₜ B) (d : V2 → V2),
      s ∈ S ∧ IsFinitePLBallPair (ℝ × ℝ) B s ∧ B ⊆ interior D ∧
      frontier B = s ∧ a.IsFinitePL ∧ FinitePiecewiseAffineOn d D ∧
      (∀ x : D, d x = (a x : V2)) ∧
      Topology.IsEmbedding (fun x : D => d x.val) ∧ d '' D = B ∧
      d '' frontier D = s ∧ (∀ x : D, d x ∈ s ↔ (x : V2) ∈ frontier D) ∧
      B ∩ (⋃ t ∈ S, t) = s ∧ Disjoint (interior B) (⋃ t ∈ S, t) := by
  obtain ⟨s, B, a, d, hs, hball, hB, hf, ha, hd, hv, hi, himg, hrimg, hrim,
    hinter, hdis, _⟩ := exists_innermost_frontier_polygon_disk_with_collar hS hne hpoly hdisj hsub
  exact ⟨s, B, a, d, hs, hball, hB, hf, ha, hd, hv, hi, himg, hrimg, hrim, hinter, hdis⟩



theorem innermost_polygon_disk_frontier_preimage
    {X : Type*} {F : Set X} {g : V2 → X} {S : Set (Set V2)}
    {B s : Set V2} {d : V2 → V2} (hBD : B ⊆ D) (hd : MapsTo d D B)
    (hinter : B ∩ (⋃ t ∈ S, t) = s)
    (hcover : D ∩ g ⁻¹' F = ⋃ t ∈ S, t)
    (hrim : ∀ x : D, d x ∈ s ↔ (x : V2) ∈ frontier D) :
    D ∩ (g ∘ d) ⁻¹' F = frontier D := by
  ext x
  constructor
  · rintro ⟨hxD, hxF⟩
    apply (hrim ⟨x, hxD⟩).mp
    apply hinter.subset
    exact ⟨hd hxD, hcover.subset ⟨hBD (hd hxD), hxF⟩⟩
  · intro hx
    have hxD : x ∈ D := isClosed_closedBall.frontier_subset hx
    have hxs : d x ∈ s := (hrim ⟨x, hxD⟩).mpr hx
    exact ⟨hxD, (hcover.superset (hinter.superset hxs).2).2⟩

end PoincareConjecture.M76
