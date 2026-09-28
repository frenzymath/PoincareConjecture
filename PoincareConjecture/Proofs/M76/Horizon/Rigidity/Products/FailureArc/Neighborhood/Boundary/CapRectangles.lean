import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.CubeCoordinates
import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductCut



set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (0 : ℝ) 1
local notation "Rect" => (I ×ˢ I : Set P2)

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X V3} {Q : Set X} {j : V2 → X}

noncomputable def capRectangle (P : OriginalDiskProduct e Q j) (s : ℝ) (p : P2) : X :=
  P.map (CubeCoordinates.fromRectangle p,s)

set_option maxHeartbeats 800000 in
theorem capRectangle_properties (P : OriginalDiskProduct e Q j)
    {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    PolyhedralPLInCharts e (capRectangle P s) Rect ∧
      IsEmbedding (fun p : Rect => capRectangle P s p) ∧
      MapsTo (capRectangle P s) Rect Q ∧
      capRectangle P s '' Rect = P.map '' (Disk ×ˢ {s}) ∧
      (∀ p ∈ Rect, capRectangle P s p ∈ frontier Q ↔ p ∈ frontier Rect) := by
  let a : V2 →ᴬ[ℝ] (V2 × ℝ) :=
    (ContinuousAffineMap.id ℝ V2).prod (ContinuousAffineMap.const ℝ V2 s)
  have hsource (p : P2) (hp : p ∈ Rect) : CubeCoordinates.fromRectangle p ∈ Disk :=
    (CubeCoordinates.toRectangle_mem_iff _).mp
      ((CubeCoordinates.toRectangle_fromRectangle p).symm ▸ hp)
  have hF := CubeCoordinates.fromRectangle_finitePL.postcomp a
  have hF' := hF
  obtain ⟨K,hK,hKs,_⟩ := hF'
  have hPL : PolyhedralPLInCharts e (capRectangle P s) Rect := by
    have h := P.polyhedral.comp_finitePiecewiseAffineOn K hK (hKs.symm ▸ hF)
      (fun p hp => show a (CubeCoordinates.fromRectangle p) ∈
        Disk ×ˢ Icc (-1 : ℝ) 1 from ⟨hsource p (hKs.subset hp),hs⟩)
    exact hKs ▸ h
  have hinj : InjOn (capRectangle P s) Rect := by
    intro p hp q hq heq
    have heq' := congrArg Prod.fst (P.injective
      ⟨hsource p hp,hs⟩ ⟨hsource q hq,hs⟩ heq)
    simpa only [CubeCoordinates.toRectangle_fromRectangle] using
      congrArg CubeCoordinates.toRectangle heq'
  let : CompactSpace Rect := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  refine ⟨hPL,(hPL.continuousOn.domRestrict.isClosedEmbedding
    (fun p q h => Subtype.ext (hinj p.property q.property h))).isEmbedding,
    fun p hp => P.inside ⟨hsource p hp,hs⟩,?_,?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨p,hp,rfl⟩
      exact ⟨(CubeCoordinates.fromRectangle p,s),⟨hsource p hp,rfl⟩,rfl⟩
    · rintro _ ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
      have hts : t = s := ht
      subst t
      exact ⟨CubeCoordinates.toRectangle z,CubeCoordinates.toRectangle_bijOn.1 hz,
        by simp only [capRectangle,CubeCoordinates.fromRectangle_toRectangle]⟩
  · intro p hp
    change P.map (CubeCoordinates.fromRectangle p,s) ∈ frontier Q ↔ _
    exact (P.proper _ ⟨hsource p hp,hs⟩).trans (by
      simpa only [CubeCoordinates.toRectangle_fromRectangle] using
        (CubeCoordinates.toRectangle_rim_iff (CubeCoordinates.fromRectangle p)).symm)

omit [T2Space X] in
theorem capRectangle_image_frontier (P : OriginalDiskProduct e Q j) (s : ℝ) :
    capRectangle P s '' frontier Rect = P.map '' (Rim ×ˢ {s}) := by
  apply Subset.antisymm
  · rintro _ ⟨p,hp,rfl⟩
    have hz : CubeCoordinates.fromRectangle p ∈ Rim :=
      (CubeCoordinates.toRectangle_rim_iff _).mp
        ((CubeCoordinates.toRectangle_fromRectangle p).symm ▸ hp)
    exact ⟨(CubeCoordinates.fromRectangle p,s),⟨hz,rfl⟩,rfl⟩
  · rintro _ ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
    have hts : t = s := ht
    subst t
    exact ⟨CubeCoordinates.toRectangle z,(CubeCoordinates.toRectangle_rim_iff z).mpr hz,
      by simp only [capRectangle,CubeCoordinates.fromRectangle_toRectangle]⟩

theorem capRectangles_disjoint (P : OriginalDiskProduct e Q j) :
    Disjoint (capRectangle P (-(1/2)) '' Rect) (capRectangle P (1/2) '' Rect) := by
  rw [(capRectangle_properties P (by norm_num : -(1/2 : ℝ) ∈ Icc (-1) 1)).2.2.2.1,
    (capRectangle_properties P (by norm_num : (1/2 : ℝ) ∈ Icc (-1) 1)).2.2.2.1]
  exact P.disjoint_end_disks

theorem capRectangles_cover_endDisks (P : OriginalDiskProduct e Q j) :
    (capRectangle P (-(1/2)) '' Rect) ∪ (capRectangle P (1/2) '' Rect) = P.endDisks := by
  rw [(capRectangle_properties P (by norm_num : -(1/2 : ℝ) ∈ Icc (-1) 1)).2.2.2.1,
    (capRectangle_properties P (by norm_num : (1/2 : ℝ) ∈ Icc (-1) 1)).2.2.2.1,
    ← image_union,← prod_union]
  rfl

theorem capRectangles_mapsTo_cut_frontier (P : OriginalDiskProduct e Q j)
    (hQ : IsCompact Q)
    (hopen : IsOpen ((Subtype.val : Q → X) ⁻¹' P.openStrip))
    {s : ℝ} (hs : s = -(1/2) ∨ s = 1/2) :
    MapsTo (capRectangle P s) Rect (frontier P.cutCarrier) := by
  have hsI : s ∈ Icc (-1 : ℝ) 1 := by rcases hs with rfl|rfl <;> norm_num
  intro p hp
  rw [(P.cut_geometry hQ hopen).2.2.1]
  apply Or.inr
  have himage := (capRectangle_properties P hsI).2.2.2.1.subset
    (mem_image_of_mem (capRectangle P s) hp)
  apply image_mono (prod_mono subset_rfl ?_) himage
  intro t ht
  have hts : t = s := ht
  simpa only [mem_insert_iff,mem_singleton_iff,hts] using hs

end PoincareConjecture.M76.Dehn.Annuli
