import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.Saddle.ConnectedLevel
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Planar.Pairing
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Strips.Family
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.CompactFiber



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





theorem exists_terminal_saddle_band_coordinates
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
    ∃ r : Real, 0 < r ∧ r < ε ∧ closedSquare r ⊆ e.source ∧
      ∃ (a b : Fin 2 → Real) (w η : Real)
          (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2),
        0 < w ∧ 0 < η ∧ η < w ∧ η < ε ∧ (∀ i, a i < b i) ∧
        (∀ i, (F i).source = Ioo (a i - w) (b i + w) ×ˢ Ioo (-w) w) ∧
        (∀ i, ContMDiffOn IR2 (𝓡 2) ∞ (F i) (F i).source) ∧
        (∀ i, ContMDiffOn (𝓡 2) IR2 ∞ (F i).symm (F i).target) ∧
        (∀ i z, z ∈ (F i).source → h (F i z) = h p + z.2) ∧
        (⋃ i, F i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real))) =
          (h ⁻¹' {h p}) \ e '' openSquare r ∧
        Pairwise (fun i j => Disjoint (F i).target (F j).target) ∧
        (∀ i, range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
            (F i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real))) =
          {F i (a i, 0), F i (b i, 0)}) ∧
        h ⁻¹' Icc (h p - η) (h p + η) ⊆ interior P.core ∧
        h ⁻¹' Icc (h p - η) (h p + η) ⊆
          e '' openSquare r ∪ ⋃ i, (F i).target ∧
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
  have hunique : ∀ q, h q = h p → mfderiv (𝓡 2) 𝓘(Real, Real) h q = 0 → q = p :=
    fun q hq hqc => M.eq_of_physical_critical_level hg P hP hcaps hp hc hq hqc
  have hcomponent : connectedComponentIn (h ⁻¹' {h p}) p = h ⁻¹' {h p} :=
    M.connectedComponentIn_physical_critical_level hg P hP hcaps hp hc
  obtain ⟨r, hr, hrε, hrs, hpair⟩ := exists_exterior_adjacent_pairing hgemb
    (mem_sphere_zero_iff_norm.mp M.v.property) p hunique e he0 hep he hei hform hε
  obtain ⟨a, b, w, F, hw, hab, hFs, hF, hFi, hheight, hcover, hdisjoint, hends, _⟩ :=
    exists_disjoint_actual_exterior_strips hh hunique e he0 hep he hei hform hr hrs
  dsimp only at hcover hpair
  change _ = connectedComponentIn (h ⁻¹' {h p}) p \ _ at hcover
  rw [hcomponent] at hcover
  change (∀ i j, _ ∈ connectedComponentIn (connectedComponentIn (h ⁻¹' {h p}) p \ _)
      _ ↔ _) ∨ (∀ i j, _ ∈ connectedComponentIn
        (connectedComponentIn (h ⁻¹' {h p}) p \ _) _ ↔ _) at hpair
  rw [hcomponent] at hpair
  let U := (e '' openSquare r ∪ ⋃ i, (F i).target) ∩ interior P.core
  have hU : IsOpen U := ((e.isOpen_image_of_subset_source (isOpen_openSquare r)
    ((openSquare_subset_closedSquare r).trans hrs)).union
      (isOpen_iUnion fun i => (F i).open_target)).inter isOpen_interior
  have hlevelU : h ⁻¹' {h p} ⊆ U := by
    intro q hq
    refine ⟨?_, M.physical_critical_level_subset_interior_core hg P hP hcaps hp hc hq⟩
    by_cases hqpatch : q ∈ e '' openSquare r
    · exact Or.inl hqpatch
    · right
      obtain ⟨i, ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩⟩ := mem_iUnion.mp (hcover.superset ⟨hq, hqpatch⟩)
      have ht0 : t = 0 := ht
      subst t
      apply mem_iUnion_of_mem i
      apply (F i).map_source
      rw [hFs i]
      exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ⟨by linarith, hw⟩⟩
  obtain ⟨δ, hδ, hband⟩ :=
    Poincare.Topology.exists_closedBand_subset_of_fiber_subset_open hh.continuous hU hlevelU
  let η := min δ (min w ε) / 2
  have hη : 0 < η := half_pos (lt_min hδ (lt_min hw hε))
  have hηδ : η ≤ δ := (half_le_self (le_min hδ.le (le_min hw.le hε.le))).trans (min_le_left _ _)
  have hηw : η < w := (half_lt_self (lt_min hδ (lt_min hw hε))).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hηε : η < ε := (half_lt_self (lt_min hδ (lt_min hw hε))).trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : h ⁻¹' Icc (h p - η) (h p + η) ⊆ U := by
    intro q hq
    apply hband
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  exact ⟨r, hr, hrε, hrs, a, b, w, η, F, hw, hη, hηw, hηε, hab, hFs,
    hF, hFi, hheight, hcover, hdisjoint, hends,
    fun q hq => (hsmall hq).2, fun q hq => (hsmall hq).1, hpair⟩

end Poincare.Manifold.Schoenflies.SphereMorseReduction
