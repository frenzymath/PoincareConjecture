import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleChartStars
import PoincareConjecture.Proofs.M76.PrimeReduction.OriginalDomainCharts
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.FrontierChartSign

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_protected_frontier_chart
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N Y F : Set X}
    (hN : PLDomain e N) (hY : IsOpen Y) (hcut : Y ∩ frontier N = F)
    (x : X) (hx : x ∈ Y) :
    ∃ B : OpenPartialHomeomorph X V3, x ∈ B.source ∧ B.source ⊆ Y ∧
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      (Disjoint B.source F ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧
        (∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)) ∧
        ∀ y ∈ B.source, y ∈ F ↔ ell (B y) = 0) := by
  by_cases hxf : x ∈ frontier N
  · obtain ⟨ell, v, C, hv, hxC, _, hcompat, hside⟩ := hN.halfspace x hxf
    let B := C.restrOpen Y hY
    have hnonzero : ell.toAffineMap.linear ≠ 0 := by
      intro hz
      have heq : ell.contLinear v = 0 := congrArg (fun a : V3 →ₗ[ℝ] ℝ => a v) hz
      rw [hv] at heq
      norm_num at heq
    have hfront := C.isImage_frontier_of_affine_nonneg ell hnonzero hside
    refine ⟨B, ⟨hxC, hx⟩, fun _ hy => hy.2, ?_,
      Or.inr ⟨ell, v, hv, fun y hy => hside y hy.1, ?_⟩⟩
    · intro i
      apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
      exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (hcompat i)).mono
        ((e i).symm.trans B).open_source (fun _ hy => ⟨hy.1, hy.2.1⟩)
    · intro y hy
      rw [← hcut, mem_inter_iff, and_iff_right hy.2]
      exact (hfront.apply_mem_iff hy.1).symm
  · obtain ⟨i, hi⟩ := hN.cover x
    let B := (e i).restrOpen (Y ∩ (frontier N)ᶜ) (hY.inter isClosed_frontier.isOpen_compl)
    refine ⟨B, ⟨hi, hx, hxf⟩, fun _ hy => hy.2.1, ?_, Or.inl ?_⟩
    · intro j
      apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
      exact ((mem_piecewiseAffineGroupoid_iff_forward _).mp (hN.compatible j i)).mono
        ((e j).symm.trans B).open_source (fun _ hy => ⟨hy.1, hy.2.1⟩)
    · exact disjoint_left.mpr fun y hy hyF => hy.2.2 (hcut.symm.subset hyF).2

theorem PLDomain.exists_protected_frontier_map_stars
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {N Y F : Set X}
    (hN : PLDomain e N) (hY : IsOpen Y) (hcut : Y ∩ frontier N = F)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space) (hfY : MapsTo f K.space Y)
    (J : κ → SimplicialComplex ℝ E) (hJ : ∀ a, (J a).faces.Finite)
    (hJK : ∀ a, (J a).space ⊆ K.space) :
    ∃ (R : SimplicialComplex ℝ E) (L : κ → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧
      (∀ a, L a ≤ R ∧ (L a).space = (J a).space ∧
        ∀ s ∈ R.faces, (∀ v ∈ s, v ∈ (L a).vertices) → s ∈ (L a).faces) ∧
      ∀ p ∈ R.vertices, ∃ B : OpenPartialHomeomorph X V3,
        B.source ⊆ Y ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        MapsTo f (R.closedStar p).space B.source ∧
        (R.closedStar p).AffineOnFaces (B ∘ f) ∧
        (Disjoint B.source F ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
          ell.contLinear v = 1 ∧
          (∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)) ∧
          ∀ y ∈ B.source, y ∈ F ↔ ell (B y) = 0) := by
  classical
  choose B hpoint hBY hcompat hkind using fun x : K.space =>
    hN.exists_protected_frontier_chart hY hcut (f x) (hfY x.property)
  obtain ⟨R, L, hR, hRK, hL, hstars⟩ :=
    hf.exists_full_compatible_chart_stars K hK B hcompat hpoint J hJ hJK
  refine ⟨R, L, hR, hRK, hL, ?_⟩
  intro p hp
  obtain ⟨x, hsource, hfaces⟩ := hstars p hp
  exact ⟨B x, hBY x, hcompat x, hsource, hfaces, hkind x⟩

end PoincareConjecture.M76
