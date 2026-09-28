import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.Saddle.Band
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Strips.PlanarClearance







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereMorseReduction

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
local notation "IR2" => 𝓘(Real, Real × Real)




theorem exists_terminal_saddle_separated_band
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    {ε : Real} (hε : 0 < ε) :
    let h := fun q => inner Real (M.v : E3) (g q)
    ∃ (r w η : Real) (a b : Fin 2 → Real)
        (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
        (U : Fin 2 → Set (Real ∙ (M.v : E3))ᗮ),
      0 < r ∧ r < ε ∧ closedSquare r ⊆ e.source ∧
      0 < w ∧ 0 < η ∧ η < w ∧ η < ε ∧ (∀ i, a i < b i) ∧
      (∀ i, (F i).source = Ioo (a i - w) (b i + w) ×ˢ Ioo (-w) w) ∧
      (∀ i, ContMDiffOn IR2 (𝓡 2) ∞ (F i) (F i).source) ∧
      (∀ i, ContMDiffOn (𝓡 2) IR2 ∞ (F i).symm (F i).target) ∧
      (∀ i z, z ∈ (F i).source → h (F i z) = h p + z.2) ∧
      (⋃ i, F i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real))) =
        (h ⁻¹' {h p}) \ e '' openSquare r ∧
      Pairwise (fun i j => Disjoint (F i).target (F j).target) ∧
      (∀ i, IsOpen (U i) ∧
        (Real ∙ (M.v : E3))ᗮ.orthogonalProjectionOnto (g p) ∉ U i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      (∀ i q, q ∈ (F i).target →
        (Real ∙ (M.v : E3))ᗮ.orthogonalProjectionOnto (g q) ∈ U i) ∧
      h ⁻¹' Icc (h p - η) (h p + η) ⊆ interior P.core ∧
      h ⁻¹' Icc (h p - η) (h p + η) ⊆
        e '' openSquare r ∪ ⋃ i, (F i).target ∧
      (∀ i, range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
          (F i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real))) =
        {F i (a i, 0), F i (b i, 0)}) ∧
      ((∀ i j : Fin 2 × Fin 2,
        e (contact r i) ∈ connectedComponentIn ((h ⁻¹' {h p}) \ e '' openSquare r)
          (e (contact r j)) ↔ i.1 = j.1) ∨
       (∀ i j : Fin 2 × Fin 2,
        e (contact r i) ∈ connectedComponentIn ((h ⁻¹' {h p}) \ e '' openSquare r)
          (e (contact r j)) ↔ i.2 = j.2)) := by
  dsimp only
  let h := fun q => inner Real (M.v : E3) (g q)
  have hgemb := M.tree.embedding_of_mem_leaves hg
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real (M.v : E3)).contMDiff.comp hgemb.contMDiff
  obtain ⟨r, hr, hrε, hrs, a, b, w, η₀, F, hw, _, _, _, hab, hFs,
      hF, hFi, hheight, hcover, hdisjoint, hends, _, _, hpair⟩ :=
    M.exists_terminal_saddle_band_coordinates hg P hP hcaps hp hc e he0 hep he hei hform hε
  have hpnot (i : Fin 2) : p ∉ F i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real)) := by
    intro hin
    have hex := hcover.subset (mem_iUnion_of_mem i hin)
    exact hex.2 (hep ▸ mem_image_of_mem e (zero_mem_openSquare hr))
  obtain ⟨d, U, G, hd, _, hGs, hG, hGi, hGF, hGheight, hU, hUdisjoint,
      hGdisjoint, hGU⟩ := exists_planarly_separated_strip_restrictions hgemb
    (mem_sphere_zero_iff_norm.mp M.v.property) p rfl a b (fun i => (hab i).le)
    hw F hFs hF hFi hheight hdisjoint hpnot
  have hGcover : (⋃ i, G i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real))) =
      (h ⁻¹' {h p}) \ e '' openSquare r := by
    have hGeq : ∀ i, (G i : (Real × Real) → S2) = F i :=
      fun i => funext (hGF i)
    simpa only [hGeq] using hcover
  let V := (e '' openSquare r ∪ ⋃ i, (G i).target) ∩ interior P.core
  have hV : IsOpen V := ((e.isOpen_image_of_subset_source (isOpen_openSquare r)
    ((openSquare_subset_closedSquare r).trans hrs)).union
      (isOpen_iUnion fun i => (G i).open_target)).inter isOpen_interior
  have hlevelV : h ⁻¹' {h p} ⊆ V := by
    intro q hq
    refine ⟨?_, M.physical_critical_level_subset_interior_core hg P hP hcaps hp hc hq⟩
    by_cases hqpatch : q ∈ e '' openSquare r
    · exact Or.inl hqpatch
    · right
      obtain ⟨i, ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩⟩ :=
        mem_iUnion.mp (hGcover.superset ⟨hq, hqpatch⟩)
      have ht0 : t = 0 := ht
      subst t
      apply mem_iUnion_of_mem i
      apply (G i).map_source
      rw [hGs i]
      exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ⟨by linarith, hd⟩⟩
  obtain ⟨δ, hδ, hband⟩ :=
    Poincare.Topology.exists_closedBand_subset_of_fiber_subset_open hh.continuous hV hlevelV
  let η := min δ (min d ε) / 2
  have hη : 0 < η := half_pos (lt_min hδ (lt_min hd hε))
  have hηδ : η ≤ δ := (half_le_self (le_min hδ.le (le_min hd.le hε.le))).trans
    (min_le_left _ _)
  have hηd : η < d := (half_lt_self (lt_min hδ (lt_min hd hε))).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hηε : η < ε := (half_lt_self (lt_min hδ (lt_min hd hε))).trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : h ⁻¹' Icc (h p - η) (h p + η) ⊆ V := by
    intro q hq
    apply hband
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  refine ⟨r, d, η, a, b, G, U, hr, hrε, hrs, hd, hη, hηd, hηε, hab,
    hGs, hG, hGi, hGheight, hGcover, hGdisjoint, hU, hUdisjoint, hGU,
    (fun q hq => (hsmall hq).2), (fun q hq => (hsmall hq).1), ?_, hpair⟩
  have hGeq : ∀ i, (G i : (Real × Real) → S2) = F i :=
    fun i => funext (hGF i)
  simpa only [hGeq] using hends

end Poincare.Manifold.Schoenflies.SphereMorseReduction

end

end M38Schoenflies
