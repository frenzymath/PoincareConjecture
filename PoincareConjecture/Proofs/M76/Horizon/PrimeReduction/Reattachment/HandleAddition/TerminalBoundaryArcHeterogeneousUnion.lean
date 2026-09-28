import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.UnionDisk.Halves
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Replacement.ArcExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Replacement.Seam

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.BoundaryUnionDisk

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

private theorem exists_original_half_charts_heterogeneous
    {X ι : Type*} (E : Bool → Type*) [TopologicalSpace X] [T2Space X]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (D U W : ∀ i, Set (E i)) (a b : ∀ i, E i) (f : ∀ i, E i → X)
    (hD : ∀ i, IsFinitePLBallPair P2 (D i) (U i ∪ W i))
    (hU : ∀ i, IsFinitePLBallPair ℝ (U i) {a i, b i})
    (hW : ∀ i, IsFinitePLBallPair ℝ (W i) {a i, b i})
    (hUW : ∀ i, U i ∩ W i = {a i, b i}) (hab : ∀ i, a i ≠ b i)
    (hf : ∀ i, PolyhedralPLInCharts e (f i) (D i)) (hfi : ∀ i, InjOn (f i) (D i))
    (himage : f false '' W false = f true '' W true)
    (ha : f false (a false) = f true (a true))
    (hb : f false (b false) = f true (b true)) :
    ∃ C : ∀ i, half i ≃ₜ D i, (∀ i, (C i).IsFinitePL) ∧
      (∀ x : seam,
        f false (C false ⟨x, (half_ball false).1 (seam_subset_frontier false x.property)⟩) =
        f true (C true ⟨x, (half_ball true).1 (seam_subset_frontier true x.property)⟩)) ∧
      (∀ i (x : half i), (C i x : E i) ∈ U i ↔ (x : P2) ∈ frontier whole) ∧
      ∀ i (x : half i), (C i x : E i) ∈ W i ↔ (x : P2) ∈ seam := by
  have hWD (i : Bool) : W i ⊆ D i := subset_union_right.trans (hD i).1
  have hfW (i : Bool) : PolyhedralPLInCharts e (f i) (W i) := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJW, _⟩, _⟩, _⟩ := hW i
    exact hJW ▸ (hf i).restrict_finite J hJ (hJW.subset.trans (hWD i))
  obtain ⟨r, hr, hrv⟩ := exists_original_interval_identification he (hW false) (hW true)
    (hfW false) (hfW true) ((hfi false).mono (hWD false))
    ((hfi true).mono (hWD true)) himage
  obtain ⟨w₀, hw₀, hw₀a, hw₀b⟩ := (hW false).exists_unitInterval_chart_with_endpoints (hab false)
  let w : ∀ i, unitInterval ≃ₜ W i := Bool.rec w₀ (w₀.trans r)
  have hw (i : Bool) : (w i).IsFinitePL := by
    cases i
    · exact hw₀
    · exact hw₀.trans hr
  have hwa (i : Bool) : (w i 0 : E i) = a i := by
    cases i
    · exact hw₀a
    · apply hfi true (hWD true (w true 0).property) (hWD true ((hW true).1 (by simp)))
      exact (hrv (w₀ 0)).symm.trans ((congrArg (f false) hw₀a).trans ha)
  have hwb (i : Bool) : (w i 1 : E i) = b i := by
    cases i
    · exact hw₀b
    · apply hfi true (hWD true (w true 1).property) (hWD true ((hW true).1 (by simp)))
      exact (hrv (w₀ 1)).symm.trans ((congrArg (f false) hw₀b).trans hb)
  obtain ⟨v, hv, hv0, hv1⟩ := seam_ball.exists_unitInterval_chart_with_endpoints
    (show ((0, 1) : P2) ≠ (0, 0) by norm_num)
  obtain ⟨V, hV⟩ := exists_half_outer_intervals
  let q (i : Bool) : seam ≃ₜ W i := v.symm.trans (w i)
  have hq (i : Bool) : (q i).IsFinitePL := hv.symm.trans (hw i)
  have hq0 (i : Bool) : (q i ⟨(0, 1), seam_ball.1 (by simp)⟩ : E i) = a i := by
    have h0 : (⟨(0, 1), seam_ball.1 (by simp)⟩ : seam) = v 0 := Subtype.ext hv0.symm
    simp only [h0, q, Homeomorph.trans_apply, v.symm_apply_apply, hwa]
  have hq1 (i : Bool) : (q i ⟨(0, 0), seam_ball.1 (by simp)⟩ : E i) = b i := by
    have h1 : (⟨(0, 0), seam_ball.1 (by simp)⟩ : seam) = v 1 := Subtype.ext hv1.symm
    simp only [h1, q, Homeomorph.trans_apply, v.symm_apply_apply, hwb]
  have hex (i : Bool) := exists_disk_homeomorph_prescribed_arc
    ((hV i).2.1.symm ▸ half_ball i) (hD i) (hV i).1 seam_ball (hU i)
    (hV i).2.2.1 (hUW i) (q i) (hq i) (hq0 i) (hq1 i)
  choose C hC hCseam hCU hCW using hex
  refine ⟨C, hC, ?_, ?_, ?_⟩
  · intro x
    rw [hCseam false x, hCseam true x]
    exact hrv (w₀ (v.symm x))
  · intro i x
    exact (hCU i x).symm.trans ((hV i).2.2.2 x x.property).symm
  · exact fun i x ↦ (hCW i x).symm

theorem exists_original_union_disk_map_heterogeneous
    {X ι : Type*} (E : Bool → Type*) [TopologicalSpace X] [T2Space X]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (D U W : ∀ i, Set (E i)) (a b : ∀ i, E i) (f : ∀ i, E i → X)
    (hD : ∀ i, IsFinitePLBallPair P2 (D i) (U i ∪ W i))
    (hU : ∀ i, IsFinitePLBallPair ℝ (U i) {a i, b i})
    (hW : ∀ i, IsFinitePLBallPair ℝ (W i) {a i, b i})
    (hUW : ∀ i, U i ∩ W i = {a i, b i}) (hab : ∀ i, a i ≠ b i)
    (hf : ∀ i, PolyhedralPLInCharts e (f i) (D i)) (hfi : ∀ i, InjOn (f i) (D i))
    (himage : f false '' W false = f true '' W true)
    (ha : f false (a false) = f true (a true))
    (hb : f false (b false) = f true (b true))
    (hcontact : (f false '' D false) ∩ (f true '' D true) = f false '' W false) :
    ∃ k : P2 → X, PolyhedralPLInCharts e k whole ∧ InjOn k whole ∧
      Topology.IsEmbedding (fun x : whole ↦ k x) ∧
      (∀ i, k '' half i = f i '' D i) ∧
      ∀ i, k '' (half i ∩ frontier whole) = f i '' U i := by
  obtain ⟨C, hC, hCseam, hCU, hCW⟩ := exists_original_half_charts_heterogeneous E he D U W a b f
    hD hU hW hUW hab hf hfi himage ha hb
  choose v hv hvval using hC
  have hhalf (i : Bool) : ∃ L : SimplicialComplex ℝ P2,
      L.faces.Finite ∧ L.space = half i := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLs, _⟩, _⟩, _⟩ := half_ball i
    exact ⟨L, hL, hLs⟩
  choose L hL hLs using hhalf
  have hvmap (i : Bool) : MapsTo (v i) (half i) (D i) := by
    intro x hx
    rw [← hvval i ⟨x, hx⟩]
    exact (C i ⟨x, hx⟩).property
  have hvi (i : Bool) : InjOn (v i) (half i) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val ((C i).injective (Subtype.ext
      ((hvval i ⟨x, hx⟩).trans (hxy.trans (hvval i ⟨y, hy⟩).symm))))
  have hvimage (i : Bool) : v i '' half i = D i := by
    apply Subset.antisymm (image_subset_iff.mpr (hvmap i))
    intro y hy
    obtain ⟨x, hx⟩ := (C i).surjective ⟨y, hy⟩
    exact ⟨x, x.property, (hvval i x).symm.trans (congrArg Subtype.val hx)⟩
  have hfv (i : Bool) : PolyhedralPLInCharts e (f i ∘ v i) (L i).space :=
    (hf i).comp_finitePiecewiseAffineOn (L i) (hL i) ((hLs i).symm ▸ hv i)
      (fun _ hx ↦ hvmap i ((hLs i).subset hx))
  have hagree (x : P2) (hx : x ∈ seam) : f false (v false x) = f true (v true x) := by
    have hx₀ := (half_ball false).1 (seam_subset_frontier false hx)
    have hx₁ := (half_ball true).1 (seam_subset_frontier true hx)
    rw [← hvval false ⟨x, hx₀⟩, ← hvval true ⟨x, hx₁⟩]
    exact hCseam ⟨x, hx⟩
  obtain ⟨k, hk, hk₀, hk₁⟩ := _root_.Dehn.exists_circle_attachment_map_union he
    (L false) (L true) (hL false) (hL true) (hfv false) (hfv true)
    (fun x hx hy ↦ hagree x (half_inter.subset ⟨(hLs false).subset hx, (hLs true).subset hy⟩))
  have hkhalf (i : Bool) : EqOn k (f i ∘ v i) (half i) := by
    cases i
    · exact hLs false ▸ hk₀
    · exact hLs true ▸ hk₁
  have hkPL : PolyhedralPLInCharts e k whole := by
    simpa only [hLs, half_union] using hk
  have hmix (x y : P2) (hx : x ∈ half false) (hy : y ∈ half true)
      (hxy : f false (v false x) = f true (v true y)) : x = y := by
    obtain ⟨z, hz, hzx⟩ := hcontact.subset
      ⟨⟨v false x, hvmap false hx, rfl⟩, ⟨v true y, hvmap true hy, hxy.symm⟩⟩
    have hzx' : z = v false x := hfi false ((hD false).1 (Or.inr hz))
      (hvmap false hx) hzx
    have hvxW : v false x ∈ W false := hzx' ▸ hz
    have hxW : x ∈ seam := (hCW false ⟨x, hx⟩).mp ((hvval false ⟨x, hx⟩).symm ▸ hvxW)
    have hx₁ := (half_ball true).1 (seam_subset_frontier true hxW)
    exact hvi true hx₁ hy (hfi true (hvmap true hx₁) (hvmap true hy)
      ((hagree x hxW).symm.trans hxy))
  have hki : InjOn k whole := by
    intro x hx y hy hxy
    rcases half_union.symm.subset hx with hx | hx <;>
      rcases half_union.symm.subset hy with hy | hy
    · exact hvi false hx hy (hfi false (hvmap false hx) (hvmap false hy)
        ((hkhalf false hx).symm.trans (hxy.trans (hkhalf false hy))))
    · exact hmix x y hx hy ((hkhalf false hx).symm.trans (hxy.trans (hkhalf true hy)))
    · exact (hmix y x hy hx ((hkhalf false hy).symm.trans
        (hxy.symm.trans (hkhalf true hx)))).symm
    · exact hvi true hx hy (hfi true (hvmap true hx) (hvmap true hy)
        ((hkhalf true hx).symm.trans (hxy.trans (hkhalf true hy))))
  let : CompactSpace whole := isCompact_iff_compactSpace.mp whole_ball.isCompact
  have hke := (hkPL.continuousOn.domRestrict.isClosedEmbedding
    (fun x y hxy ↦ Subtype.ext (hki x.property y.property hxy))).isEmbedding
  have hvU (i : Bool) (x : P2) (hx : x ∈ half i) :
      v i x ∈ U i ↔ x ∈ frontier whole := by
    rw [← hvval i ⟨x, hx⟩]
    exact hCU i ⟨x, hx⟩
  refine ⟨k, hkPL, hki, hke, ?_, ?_⟩
  · intro i
    rw [image_congr (hkhalf i), image_comp, hvimage i]
  · intro i
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨v i x, (hvU i x hx.1).mpr hx.2, (hkhalf i hx.1).symm⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := (hvimage i).symm.subset ((hD i).1 (Or.inl hy))
      exact ⟨x, ⟨hx, (hvU i x hx).mp (hxy.symm ▸ hy)⟩,
        (hkhalf i hx).trans (congrArg (f i) hxy)⟩

end PoincareConjecture.M76.Dehn.Annuli.BoundaryUnionDisk
