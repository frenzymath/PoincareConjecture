import PoincareConjecture.Proofs.M76.Rigidity.CompatibleChartPatch
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedPatchImage
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.FinitePlanePatchAt

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem exists_original_interior_disk_pair_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ V2) (hK : K.faces.Finite)
    {f : V2 → X} (hf : PolyhedralPLInCharts e f K.space)
    (hemb : Topology.IsEmbedding (fun z : K.space => f z))
    (G : OpenPartialHomeomorph X V3)
    (hcompat : ∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3)
    (z : K.space) (hzint : (z : V2) ∈ interior K.space)
    (hzG : f z ∈ G.source) {U : Set X} (hU : IsOpen U) (hfzU : f z ∈ U) :
    ∃ H : OpenPartialHomeomorph X C3,
      f z ∈ H.source ∧ H.source ⊆ U ∩ G.source ∧
      H.target = interior (CoordinateHalfBoxes.box 1) ∧ H (f z) = 0 ∧
      (∀ x ∈ H.source, x ∈ f '' K.space ↔ (H x).2 = 0) ∧
      ∀ i,
        LocallyPiecewiseAffineOn ((e i).symm.trans H) ((e i).symm.trans H).source ∧
        LocallyPiecewiseAffineOn (H.symm.trans (e i)) (H.symm.trans (e i)).source := by
  obtain ⟨N, W, hN, hNK, hW, hzW, hWN, hNG, hcoords⟩ :=
    hf.exists_finite_compatible_chart_patch K hK G hcompat z hzG
  have hzNint : (z : V2) ∈ interior N.space := by
    obtain ⟨A, hA, hAW⟩ := isOpen_induced_iff.mp hW
    have hzA : (z : V2) ∈ A := by
      change z ∈ (Subtype.val : K.space → V2) ⁻¹' A
      rwa [hAW]
    have hAN : A ∩ interior K.space ⊆ N.space := by
      intro x hx
      have hxW : (⟨x, interior_subset hx.2⟩ : K.space) ∈ W := by
        rw [← hAW]
        exact hx.1
      exact hWN ⟨⟨x, interior_subset hx.2⟩, hxW, rfl⟩
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset ((hA.inter isOpen_interior).mem_nhds ⟨hzA, hzint⟩) hAN)
  have hinj : InjOn (G ∘ f) N.space := by
    intro x hx y hy hxy
    have hfxy : f x = f y := G.injOn (hNG hx) (hNG hy) hxy
    have hxy' : (⟨x, hNK hx⟩ : K.space) = ⟨y, hNK hy⟩ := hemb.injective hfxy
    exact congrArg Subtype.val hxy'
  obtain ⟨O, hO, hzO, hOt, hfull⟩ :=
    hemb.exists_open_chart_image_eq_of_patch G hNK hNG z W hW hzW hWN
  let V := O ∩ G '' (U ∩ G.source)
  let S := G '' (f '' K.space ∩ G.source)
  have hV : IsOpen V := hO.inter
    (G.isOpen_image_of_subset_source (hU.inter G.open_source) inter_subset_right)
  have hzV : G (f z) ∈ V := ⟨hzO, ⟨f z, ⟨hfzU, hzG⟩, rfl⟩⟩
  have hVt : V ⊆ G.target := fun x hx => hOt hx.1
  have hfullV : S ∩ V = ((G ∘ f) '' N.space) ∩ V := by
    ext x
    exact ⟨fun hx => ⟨(hfull.subset ⟨hx.1, hx.2.1⟩).1, hx.2⟩,
      fun hx => ⟨(hfull.symm.subset ⟨hx.1, hx.2.1⟩).1, hx.2⟩⟩
  obtain ⟨C, hzC, hCV, hCt, hC, hCi, hCz, hCS⟩ :=
    HamiltonIndexOne.exists_pair_chart_of_finitePL_plane_patch_at (by simp)
      hcoords hinj hzNint hV hzV hfullV
  let H := G.trans C
  have hHt : H.target = C.target := by
    apply inter_eq_left.mpr
    intro x hx
    exact hVt (hCV (C.map_target hx))
  have hHU : H.source ⊆ U ∩ G.source := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (hCV hx.2).2
    exact ⟨G.injOn hy.2 hx.1 hyx ▸ hy.1, hx.1⟩
  refine ⟨H, ⟨hzG, hzC⟩, hHU, hHt.trans hCt, hCz, ?_, ?_⟩
  · intro x hx
    have hmem : x ∈ f '' K.space ↔ G x ∈ S := by
      constructor
      · intro hxS
        exact ⟨x, ⟨hxS, hx.1⟩, rfl⟩
      · rintro ⟨y, ⟨hyS, hyG⟩, hyx⟩
        exact G.injOn hyG hx.1 hyx ▸ hyS
    exact hmem.trans (hCS (G x) hx.2)
  · intro i
    have hc := (mem_piecewiseAffineGroupoid_iff V3 _).mp (hcompat i)
    have hforward : LocallyPiecewiseAffineOn (((e i).symm.trans G).trans C)
        (((e i).symm.trans G).trans C).source := hC.comp hc.1
    have hinverse : LocallyPiecewiseAffineOn (C.symm.trans (G.symm.trans (e i)))
        (C.symm.trans (G.symm.trans (e i))).source := hc.2.comp hCi
    constructor
    · simpa only [H, OpenPartialHomeomorph.trans_assoc] using hforward
    · simpa only [H, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hinverse

end PoincareConjecture.M76
