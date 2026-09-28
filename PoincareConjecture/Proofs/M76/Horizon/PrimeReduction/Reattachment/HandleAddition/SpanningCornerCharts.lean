import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.CornerCorrection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningProtectedCorner
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.SpanningCornerSides

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

theorem OriginalSurfacePairChart.exists_convex_restriction
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {D T : Set X} {x : X} {b : Bool}
    (B : OriginalSurfacePairChart e D T x b) :
    ∃ C : OriginalSurfacePairChart e D T x b,
      C.chart = B.chart ∧ Convex ℝ C.coordinates.target ∧
      C.coordinates.source ⊆ B.coordinates.source ∧
      (∀ z, C.coordinates z = B.coordinates z) := by
  obtain ⟨G,hxG,hG0,hcv,hGB,hGt,_,hval,hinv⟩ :=
    B.coordinates.exists_convex_target_avoiding B.center_coordinates B.center_zero
      isClosed_empty (notMem_empty _)
  let C : OriginalSurfacePairChart e D T x b := {
    chart := B.chart
    coordinates := G
    compatible := B.compatible
    center_source := B.center_source
    center_coordinates := hxG
    center_zero := hG0
    source_subset := hGB.trans B.source_subset
    forwardPL := (B.forwardPL.mono G.open_source hGB).congr (fun z _ => (hval z).symm)
    inversePL := (B.inversePL.mono G.open_target hGt).congr (fun z _ => (hinv z).symm)
    first_surface := fun z hz => by rw [hval]; exact B.first_surface z (hGB hz)
    second_surface := fun z hz => by rw [hval]; exact B.second_surface z (hGB hz) }
  exact ⟨C,rfl,hcv,hGB,hval⟩

theorem OriginalSurfacePairChart.exists_bigon_corner_restriction
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {D E W : Set X} {x : X}
    (hW : PLDomain e W)
    (B : OriginalSurfacePairChart e D (frontier W ∩ E) x true)
    (hE : ∀ z ∈ B.coordinates.source,
      B.chart.symm z ∈ E ↔ 0 ≤ (B.coordinates z).1.2)
    (hEF : ∀ z ∈ B.coordinates.source,
      B.chart.symm z ∈ frontier E ↔ (B.coordinates z).1.2 = 0) :
    ∃ (C : OriginalSurfacePairChart e D (frontier W ∩ E) x true) (ε : ℝ),
      (ε = -1 ∨ ε = 1) ∧
      (∀ z ∈ C.coordinates.source,
        C.chart.symm z ∈ frontier E ↔ (C.coordinates z).1.2 = 0) ∧
      ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ frontier (E ∩ W) ↔
        ((C.coordinates z).1.2 = 0 ∧ 0 ≤ ε * (C.coordinates z).1.1) ∨
          ((C.coordinates z).1.1 = 0 ∧ 0 ≤ (C.coordinates z).1.2) := by
  obtain ⟨C,hchart,hcv,hsource,hval⟩ := B.exists_convex_restriction
  let H := C.chart.trans C.coordinates
  have hHt : H.target = C.coordinates.target := by
    change C.coordinates.target ∩ C.coordinates.symm ⁻¹' C.chart.target = C.coordinates.target
    exact inter_eq_left.mpr (fun _ hz => C.source_subset (C.coordinates.map_target hz))
  have hHE (y : X) (hy : y ∈ H.source) : y ∈ E ↔ 0 ≤ (H y).1.2 := by
    have hh := hE (C.chart y) (hsource hy.2)
    rw [←hchart, C.chart.left_inv hy.1] at hh
    change y ∈ E ↔ 0 ≤ (C.coordinates (C.chart y)).1.2
    rw [hval]
    exact hh
  have hHW (y : X) (hy : y ∈ H.source) : y ∈ frontier W ∩ E ↔
      (H y).1.1 = 0 ∧ 0 ≤ (H y).1.2 := by
    have hh := C.second_surface (C.chart y) hy.2
    simpa only [H,OpenPartialHomeomorph.trans_apply,C.chart.left_inv hy.1,forall_const] using hh
  obtain ⟨ε,hε,_,hfront⟩ := signed_corner_of_relative_frontier hW.closed hW.closure_interior
    H (hHt.symm ▸ hcv) ⟨C.center_source,C.center_coordinates⟩ C.center_zero hHE hHW
  refine ⟨C,ε,hε.symm,?_,?_⟩
  · intro z hz
    rw [hval,hchart]
    exact hEF z (hsource hz)
  · intro z hz
    have hzC := C.source_subset hz
    have hys : C.chart.symm z ∈ H.source :=
      ⟨C.chart.map_target hzC,by
        change C.chart (C.chart.symm z) ∈ C.coordinates.source
        rwa [C.chart.right_inv hzC]⟩
    have hh := hfront (C.chart.symm z) hys
    simpa only [H,OpenPartialHomeomorph.trans_apply,C.chart.right_inv hzC] using hh

theorem frontier_inter_of_closed_domains
    {X : Type*} [TopologicalSpace X] {E W : Set X}
    (hE : IsClosed E) (hW : IsClosed W) :
    frontier (E ∩ W) = (E ∩ W) ∩ (frontier E ∪ frontier W) := by
  rw [frontier, (hE.inter hW).closure_eq, interior_inter,
    frontier, hE.closure_eq, frontier, hW.closure_eq]
  ext x
  simp only [mem_sdiff, mem_inter_iff, mem_union]
  tauto

theorem exists_original_bigon_rim_endpoints
    {X F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {d U C : Set F} {a b : F}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (U ∪ C))
    (hab : a ≠ b) (hUC : U ∩ C = {a,b})
    (H : Disk ≃ₜ d)
    (hHrim : ∀ z : Disk, (z : V2) ∈ Rim ↔ (H z : F) ∈ U ∪ C)
    {j : V2 → X} {S T : Set X}
    (hjS : ∀ z : Disk, j z ∈ S ↔ (H z : F) ∈ U)
    (hjT : ∀ z : Disk, j z ∈ T ↔ (H z : F) ∈ C) :
    ∃ (ends : Bool → V2) (hends : ∀ i, ends i ∈ Rim),
      ends false ≠ ends true ∧
      (∀ z ∈ Rim, j z ∈ S ∩ T ↔ ∃ i : Bool, z = ends i) ∧
      (H ⟨ends false, sphere_subset_closedBall (hends false)⟩ : F) = a ∧
      (H ⟨ends true, sphere_subset_closedBall (hends true)⟩ : F) = b := by
  have haU : a ∈ U := (hUC.symm.subset (by simp)).1
  have hbU : b ∈ U := (hUC.symm.subset (by simp)).1
  let ea : Disk := H.symm ⟨a,hd.1 (Or.inl haU)⟩
  let eb : Disk := H.symm ⟨b,hd.1 (Or.inl hbU)⟩
  have hea : (H ea : F) = a := congrArg Subtype.val (H.apply_symm_apply _)
  have heb : (H eb : F) = b := congrArg Subtype.val (H.apply_symm_apply _)
  have heai : (ea : V2) ∈ Rim := (hHrim ea).mpr (hea.symm ▸ Or.inl haU)
  have hebi : (eb : V2) ∈ Rim := (hHrim eb).mpr (heb.symm ▸ Or.inl hbU)
  let ends : Bool → V2 := fun i => if i then eb else ea
  have hends : ∀ i, ends i ∈ Rim := by intro i; cases i <;> assumption
  refine ⟨ends,hends,?_,?_,hea,heb⟩
  · intro h
    exact hab (hea.symm.trans ((congrArg (fun z : Disk => (H z : F))
      (Subtype.ext h)).trans heb))
  · intro z hz
    have hmem : j z ∈ S ∩ T ↔ (H ⟨z,sphere_subset_closedBall hz⟩ : F) ∈ ({a,b} : Set F) := by
      rw [←hUC]
      exact and_congr (hjS ⟨z,sphere_subset_closedBall hz⟩) (hjT ⟨z,sphere_subset_closedBall hz⟩)
    rw [hmem]
    constructor
    · intro h
      rcases h with h | h
      · exact ⟨false,congrArg Subtype.val (H.injective (Subtype.ext (h.trans hea.symm)))⟩
      · exact ⟨true,congrArg Subtype.val (H.injective (Subtype.ext (h.trans heb.symm)))⟩
    · rintro ⟨i,rfl⟩
      cases i
      · exact Or.inl hea
      · exact Or.inr heb

theorem OriginalDiskProduct.exists_original_bigon_marked_correction
    {X ι F : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e : ι → OpenPartialHomeomorph X V3} {E W D : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e (E ∩ W) j)
    (heN : PLDomain e (E ∩ W)) (hE : IsClosed E) (hW : PLDomain e W)
    (hopen : ∀ v : ℝ, 0 < v → v ≤ 1 →
      IsOpen ((Subtype.val : ↥(E ∩ W) → X) ⁻¹' (P.map '' (Disk ×ˢ Ioo (-v) v))) ∧
      IsOpen ((Subtype.val : frontier (E ∩ W) → X) ⁻¹' (P.map '' (Rim ×ˢ Ioo (-v) v))))
    {d U C : Set F} {a b : F}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (U ∪ C)) (hab : a ≠ b) (hUC : U ∩ C = {a,b})
    (H : Disk ≃ₜ d)
    (hHrim : ∀ z : Disk, (z : V2) ∈ Rim ↔ (H z : F) ∈ U ∪ C)
    (hjF : ∀ z : Disk, j z ∈ frontier E ↔ (H z : F) ∈ U)
    (hjW : ∀ z : Disk, j z ∈ frontier W ↔ (H z : F) ∈ C)
    (hjD : j '' Disk ⊆ D)
    (hboundary : ∀ x ∈ frontier W ∩ frontier E, x ∈ D →
      ∃ B : OriginalSurfacePairChart e D (frontier W ∩ E) x true,
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ E ↔ 0 ≤ (B.coordinates z).1.2) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier E ↔ (B.coordinates z).1.2 = 0) :
    ∃ P' : OriginalDiskProduct e (E ∩ W) j,
      P'.map '' (Disk ×ˢ Icc (-1 : ℝ) 1) ⊆ P.map '' (Disk ×ˢ Icc (-1 : ℝ) 1) ∧
      (∀ z ∈ Rim, ∀ t ∈ Icc (-1 : ℝ) 1,
        (P'.map (z,t) ∈ frontier E ↔ j z ∈ frontier E) ∧
        (P'.map (z,t) ∈ frontier W ↔ j z ∈ frontier W)) ∧
      ∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : ↥(E ∩ W) → X) ⁻¹' (P'.map '' (Disk ×ˢ Ioo (-v) v))) := by
  obtain ⟨ends,hends,hne,hseam,_,_⟩ :=
    exists_original_bigon_rim_endpoints hd hab hUC H hHrim hjF hjW
  have hjE (z : V2) (hz : z ∈ Disk) : j z ∈ E := by
    rw [←P.central z hz]
    exact (P.inside ⟨hz,by norm_num⟩).1
  have hendcontact (i : Bool) : j (ends i) ∈ frontier W ∩ frontier E := by
    have h := (hseam (ends i) (hends i)).mpr ⟨i,rfl⟩
    exact ⟨h.2,h.1⟩
  have hcorners (i : Bool) :
      ∃ (B : OriginalSurfacePairChart e D (frontier W ∩ E) (j (ends i)) true) (ε : ℝ),
        (ε = -1 ∨ ε = 1) ∧
        (∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier E ↔ (B.coordinates z).1.2 = 0) ∧
        ∀ z ∈ B.coordinates.source, B.chart.symm z ∈ frontier (E ∩ W) ↔
          ((B.coordinates z).1.2 = 0 ∧ 0 ≤ ε * (B.coordinates z).1.1) ∨
            ((B.coordinates z).1.1 = 0 ∧ 0 ≤ (B.coordinates z).1.2) := by
    obtain ⟨B,hBE,hBF⟩ := hboundary (j (ends i)) (hendcontact i)
      (hjD ⟨ends i,sphere_subset_closedBall (hends i),rfl⟩)
    exact B.exists_bigon_corner_restriction hW hBE hBF
  choose B ε hε hBFront hBN using hcorners
  have hcover : frontier (E ∩ W) ⊆ frontier E ∪ (frontier W ∩ E) := by
    rw [frontier_inter_of_closed_domains hE hW.closed]
    rintro x ⟨hx,hxf | hxw⟩
    · exact Or.inl hxf
    · exact Or.inr ⟨hxw,hx.1⟩
  have hseam' (z : V2) (hz : z ∈ Rim) :
      j z ∈ frontier E ∩ (frontier W ∩ E) ↔ ∃ i : Bool, z = ends i := by
    rw [←hseam z hz]
    exact and_congr_right (fun _ => and_iff_left (hjE z (sphere_subset_closedBall hz)))
  obtain ⟨P',hsub,hmarks,hopen'⟩ := P.exists_sheet_preserving_correction_of_corner_charts
    heN hopen isClosed_frontier (isClosed_frontier.inter hE) hcover ends hends hne hseam'
    hjD B ε hε hBFront hBN
  refine ⟨P',hsub,?_,hopen'⟩
  intro z hz t ht
  have hleft := (P'.inside (x := (z,t)) ⟨sphere_subset_closedBall hz,ht⟩).1
  have hright := hjE z (sphere_subset_closedBall hz)
  exact ⟨(hmarks z hz t ht).1,
    (and_iff_left hleft).symm.trans ((hmarks z hz t ht).2.trans (and_iff_left hright))⟩

end PoincareConjecture.M76
