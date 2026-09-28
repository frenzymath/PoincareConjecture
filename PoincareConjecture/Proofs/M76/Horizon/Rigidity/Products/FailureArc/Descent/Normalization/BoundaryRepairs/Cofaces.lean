import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Parameter
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.BoundaryOperationCofaces

set_option autoImplicit false
open Set Metric Geometry Topology unitInterval PLAnnularStrip

namespace Geometry.SimplicialComplex

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Rim" => Set.ofPred (fun z : P2 => depth 8 z = -1 ∨ depth 8 z = 1)

theorem exists_unique_annulus_boundary_triangle_germ
    (B K : SimplicialComplex ℝ V3) (hB : B.faces.Finite) (hKB : K ≤ B)
    {q : V3 → P2} (hq : B.AffineOnFaces q) (hqi : InjOn q B.space)
    (hqD : MapsTo q B.space Ann)
    (hqrim : ∀ z ∈ B.space, z ∈ K.space ↔ q z ∈ Rim)
    (edge : Finset V3) (hedge : edge ∈ K.faces) (he2 : edge.card = 2)
    (z : V3) (hze : z ∈ intrinsicInterior ℝ (convexHull ℝ (edge : Set V3)))
    (hclosure : q z ∈ closure (interior (q '' B.space))) :
    ∃ face ∈ B.faces, edge ⊆ face ∧ face.card = 3 ∧
      (∀ other ∈ B.faces, edge ⊆ other → other ⊆ face) ∧
      ∀ O : Set V3, IsOpen O → z ∈ O →
        ∃ V : Set V3, IsOpen V ∧ z ∈ V ∧ V ⊆ O ∧
          ∀ x ∈ V, x ∈ B.space ↔ x ∈ convexHull ℝ (face : Set V3) := by
  classical
  have heB := hKB hedge
  have hzK := K.convexHull_subset_space hedge (intrinsicInterior_subset hze)
  have hzB := space_subset_of_le hKB hzK
  have hzRim : q z ∈ Rim := (hqrim z hzB).mp hzK
  let N := hq.embeddedImage hqi
  have hN : N.faces.Finite := hq.embeddedImage_finite hqi hB
  have hNs : N.space = q '' B.space := hq.embeddedImage_space hqi
  have hND : N.space ⊆ Ann := by
    rw [hNs]
    rintro _ ⟨x, hx, rfl⟩
    exact hqD hx
  have hqz : q z ∈ closure (interior N.space) := hNs.symm ▸ hclosure
  have hface (u : Finset V3) (hu : u ∈ B.faces) : u.image q ∈ N.faces :=
    (hq.image_mem_embeddedImage_iff hqi (B.subset_space hu)).mpr hu
  have hcard (u : Finset V3) (hu : u ∈ B.faces) : (u.image q).card = u.card :=
    Finset.card_image_iff.mpr (hqi.mono (B.subset_space hu))
  have hqedge : q z ∈ intrinsicInterior ℝ (convexHull ℝ (edge.image q : Set P2)) := by
    obtain ⟨a, ha⟩ := hq edge heB
    have hai : InjOn a (convexHull ℝ (edge : Set V3)) := by
      intro x hx y hy hxy
      exact hqi (B.convexHull_subset_space heB hx) (B.convexHull_subset_space heB hy)
        ((ha hx).trans (hxy.trans (ha hy).symm))
    have hspan := a.toAffineMap.injOn_affineSpan_of_injOn_convex
      (convex_convexHull ℝ (edge : Set V3)) ⟨z, intrinsicInterior_subset hze⟩ hai
    rw [Finset.coe_image, ← hq.image_convexHull heB, ha.image_eq,
      ha (intrinsicInterior_subset hze), ← intrinsicClosure_sdiff_intrinsicFrontier]
    refine ⟨subset_intrinsicClosure (mem_image_of_mem a (intrinsicInterior_subset hze)), ?_⟩
    intro hfrontier
    have himagefront := a.toAffineMap.intrinsicFrontier_image_of_injOn
      (convexHull ℝ (edge : Set V3)) hspan
    obtain ⟨y, hy, hyz⟩ := himagefront.subset hfrontier
    have hyspan : y ∈ affineSpan ℝ (convexHull ℝ (edge : Set V3)) :=
      intrinsicClosure_subset_affineSpan (by
        rw [← intrinsicClosure_sdiff_intrinsicInterior] at hy
        exact hy.1)
    have heq : y = z := hspan hyspan
      (subset_affineSpan ℝ _ (intrinsicInterior_subset hze)) hyz
    rw [heq, ← intrinsicClosure_sdiff_intrinsicInterior] at hy
    exact hy.2 hze
  obtain ⟨face', hface', hfacecard, hzface'⟩ :=
    N.exists_full_face_of_mem_closure_interior hN hqz
  change face' ∈ (hq.embeddedImage hqi).faces at hface'
  rw [hq.embeddedImage_faces hqi] at hface'
  obtain ⟨face, hfaceB, rfl⟩ := hface'
  have hface3 : face.card = 3 := by
    rw [hcard face hfaceB] at hfacecard
    simpa using hfacecard
  have hzface : z ∈ convexHull ℝ (face : Set V3) := by
    rw [Finset.coe_image, ← hq.image_convexHull hfaceB] at hzface'
    obtain ⟨y, hy, hyz⟩ := hzface'
    exact hqi (B.convexHull_subset_space hfaceB hy) hzB hyz ▸ hy
  have hef : edge ⊆ face := B.subset_of_mem_intrinsicInterior_face heB hfaceB hze hzface
  have hunique (other : Finset V3) (hother : other ∈ B.faces)
      (heo : edge ⊆ other) (ho3 : other.card = 3) : other = face := by
    by_contra hne
    have himagene : other.image q ≠ face.image q := by
      intro heq
      apply hne
      apply Finset.coe_injective
      apply (hqi.image_eq_image_iff (B.subset_space hother) (B.subset_space hfaceB)).mp
      exact (Finset.coe_image.symm.trans
        (congrArg (fun a : Finset P2 => (a : Set P2)) heq)).trans Finset.coe_image
    have hinterior := N.mem_interior_space_of_paired_facet
      (by rw [hcard edge heB, he2]; simp)
      (hface other hother) (hface face hfaceB)
      (by rw [hcard other hother, ho3]; simp)
      (by rw [hcard face hfaceB, hface3]; simp)
      (Finset.image_subset_image heo) (Finset.image_subset_image hef) himagene hqedge
    have hrimfront : q z ∈ frontier Ann :=
      (PoincareConjecture.M76.Dehn.Annuli.mem_frontier_planar_annulus_iff _).mpr hzRim
    exact hrimfront.2 (interior_mono hND hinterior)
  have hexhaust (other : Finset V3) (hother : other ∈ B.faces)
      (heo : edge ⊆ other) : other ⊆ face := by
    have hupper : other.card ≤ 3 := by
      simpa using hq.face_card_le_of_injOn hqi hother
    have hlower := Finset.card_le_card heo
    by_cases htwo : other.card = 2
    · have heq : edge = other := Finset.eq_of_subset_of_card_le heo (by omega)
      exact heq ▸ hef
    · have hthree : other.card = 3 := by omega
      rw [hunique other hother heo hthree]
  refine ⟨face, hfaceB, hef, hface3, hexhaust, ?_⟩
  intro O hO hzO
  obtain ⟨V, hV, hzV, hcarrier⟩ := B.exists_open_two_coface_carrier_germ
    hB heB hfaceB hfaceB (fun u hu heu => Or.inl (hexhaust u hu heu)) hze
  refine ⟨V ∩ O, hV.inter hO, ⟨hzV, hzO⟩, inter_subset_right, ?_⟩
  intro x hx
  simpa only [union_self] using hcarrier x hx.1

end Geometry.SimplicialComplex

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

theorem exists_moved_boundary_cofaces (hj : PolyhedralPLInCharts t.charts j Ann) :
    ∃ B K : SimplicialComplex ℝ V3,
      B.faces.Finite ∧ K.faces.Finite ∧ K ≤ B ∧ A.fixedRim ≤ K ∧
      K.vertices = A.motion.map 1 '' A.rimComplex.vertices ∧
      B.space = A.motion.map 1 '' A.source.space ∧
      K.space = A.motion.map 1 '' A.boundary.space ∧
      K.space = B.space ∩ {z | (A.coordinates z).1.1 = 0} ∧
      B.AffineOnFaces (A.parameter ∘ (A.motion.map 1).symm) ∧
      InjOn (A.parameter ∘ (A.motion.map 1).symm) B.space ∧
      MapsTo (A.parameter ∘ (A.motion.map 1).symm) B.space Ann ∧
      (∀ z ∈ B.space, z ∈ K.space ↔ (A.parameter ∘ (A.motion.map 1).symm) z ∈ Rim) ∧
      ∀ edge ∈ K.faces, edge.card = 2 → ∀ z,
        z ∈ intrinsicInterior ℝ (convexHull ℝ (edge : Set V3)) →
        z ∈ interior A.support.space →
        ∃ face ∈ B.faces, edge ⊆ face ∧ face.card = 3 ∧
          (∀ other ∈ B.faces, edge ⊆ other → other ⊆ face) ∧
          ∀ O : Set V3, IsOpen O → z ∈ O →
            ∃ V : Set V3, IsOpen V ∧ z ∈ V ∧ V ⊆ O ∩ interior A.support.space ∧
              ∀ x ∈ V, x ∈ B.space ↔ x ∈ convexHull ℝ (face : Set V3) := by
  obtain ⟨B, K, hB, hK, hKB, hfixed, _, _, hvertices, hBs, hKs, hlevel,
    hq, hqi, hqD, hqrim⟩ := A.exists_moved_complexes
  refine ⟨B, K, hB, hK, hKB, hfixed, hvertices, hBs, hKs, hlevel,
    hq, hqi, hqD, hqrim, ?_⟩
  intro edge hedge he2 z hze hzJ
  have hzB := SimplicialComplex.space_subset_of_le hKB
    (K.convexHull_subset_space hedge (intrinsicInterior_subset hze))
  have hinv : (A.motion.map 1).symm z ∈ A.source.space := by
    obtain ⟨x, hx, rfl⟩ := hBs.subset hzB
    simpa only [(A.motion.map 1).symm_apply_apply] using hx
  have hinvJ : (A.motion.map 1).symm z ∈ interior A.support.space := by
    have hi := ((A.motion.map 1).image_interior A.support.space).trans
      (congrArg interior (A.motion.carrier 1))
    obtain ⟨x, hx, rfl⟩ := hi.symm.subset hzJ
    simpa only [(A.motion.map 1).symm_apply_apply] using hx
  have himage : (A.parameter ∘ (A.motion.map 1).symm) '' B.space =
      A.parameter '' A.source.space := by
    rw [hBs, image_image]
    congr 1
    funext x
    exact congrArg A.parameter ((A.motion.map 1).symm_apply_apply x)
  have hclosure : (A.parameter ∘ (A.motion.map 1).symm) z ∈
      closure (interior ((A.parameter ∘ (A.motion.map 1).symm) '' B.space)) := by
    rw [himage]
    exact A.parameter_mem_closure_interior hj _ hinv hinvJ
  obtain ⟨face, hf, hef, hf3, hexhaust, hgerm⟩ :=
    SimplicialComplex.exists_unique_annulus_boundary_triangle_germ B K hB hKB hq hqi
      hqD hqrim edge hedge he2 z hze hclosure
  refine ⟨face, hf, hef, hf3, hexhaust, ?_⟩
  intro O hO hzO
  exact hgerm (O ∩ interior A.support.space) (hO.inter isOpen_interior) ⟨hzO, hzJ⟩

end Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion
