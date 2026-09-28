import PoincareConjecture.Proofs.M76.Mathlib.CompatibleChartPLMaps
import PoincareConjecture.Proofs.M76.Mathlib.HyperplaneSubdivision

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

theorem exists_finite_PL_boundary_chart_cover
    {M E ι : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph M E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {f : M → ℝ}
    (hf : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    {R S : Set M} (hS : IsCompact S) (hSR : S ⊆ frontier R)
    (hboundary : ∀ x ∈ frontier R,
      ∃ (psi : E →ᴬ[ℝ] ℝ) (u : E) (B : OpenPartialHomeomorph M E),
        psi.contLinear u = 1 ∧ x ∈ B.source ∧ psi (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ psi (B y)) :
    ∃ (s : Finset S) (B : s → OpenPartialHomeomorph M E)
      (psi : s → E →ᴬ[ℝ] ℝ) (u : s → E) (K : s → SimplicialComplex ℝ E),
      (∀ i, (psi i).contLinear (u i) = 1) ∧
      (∀ i, (K i).faces.Finite) ∧
      (∀ i, (K i).space ⊆ (B i).target) ∧
      (∀ i, (K i).AffineOnFaces (f ∘ (B i).symm)) ∧
      (∀ i, (K i).RespectsAffineHyperplane (psi i).toAffineMap) ∧
      (∀ i j, (e j).symm.trans (B i) ∈ piecewiseAffineGroupoid E) ∧
      (∀ i y, y ∈ (B i).source → (y ∈ R ↔ 0 ≤ psi i (B i y))) ∧
      ∀ x ∈ S, ∃ i, x ∈ (B i).source ∧ B i x ∈ interior (K i).space := by
  classical
  have hchoose (x : S) :
      ∃ (psi : E →ᴬ[ℝ] ℝ) (u : E) (B : OpenPartialHomeomorph M E)
        (K : SimplicialComplex ℝ E),
        psi.contLinear u = 1 ∧ (x : M) ∈ B.source ∧ B x ∈ interior K.space ∧
        K.faces.Finite ∧ K.space ⊆ B.target ∧ K.AffineOnFaces (f ∘ B.symm) ∧
        K.RespectsAffineHyperplane psi.toAffineMap ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ psi (B y) := by
    obtain ⟨psi, u, B, hnorm, hxB, _, hBPL, hBR⟩ := hboundary x (hSR x.property)
    obtain ⟨K, hK, hxK, hKt, hfK⟩ :=
      locallyPiecewiseAffineOn_compatible_chart e hcover hf B hBPL
        (B x) (B.mapsTo hxB)
    let N := hK.toFinset.sup Finset.card
    have hN (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ N + 1 :=
      (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
    obtain ⟨L, hL, hLK, _, hLpsi⟩ :=
      K.exists_subdivision_respectsAffineHyperplanes hK hN {psi.toAffineMap}
    refine ⟨psi, u, B, L, hnorm, hxB, ?_, hL, ?_, hLK.affineOnFaces hfK,
      hLpsi psi.toAffineMap (Finset.mem_singleton_self _), hBPL, hBR⟩
    · rwa [hLK.space_eq]
    · rw [hLK.space_eq]
      exact hKt
  choose psi u B K hnorm hxB hxK hK hKt hfK hKpsi hBPL hBR using hchoose
  let V : S → Set M := fun x => (B x).source ∩ (B x) ⁻¹' interior (K x).space
  have hV (x : S) : IsOpen (V x) :=
    (B x).continuousOn_toFun.isOpen_inter_preimage (B x).open_source isOpen_interior
  have hxV (x : S) : (x : M) ∈ V x := ⟨hxB x, hxK x⟩
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover V hV
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  refine ⟨s, (fun i => B i.val), (fun i => psi i.val), (fun i => u i.val),
    (fun i => K i.val), (fun i => hnorm i.val), (fun i => hK i.val),
    (fun i => hKt i.val), (fun i => hfK i.val), (fun i => hKpsi i.val),
    (fun i => hBPL i.val), (fun i => hBR i.val), ?_⟩
  intro x hx
  obtain ⟨q, hqs, hxq⟩ := mem_iUnion₂.mp (hs hx)
  exact ⟨⟨q, hqs⟩, hxq⟩

end OpenPartialHomeomorph
