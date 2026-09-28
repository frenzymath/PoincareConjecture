import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.Saddle.SeparatedBand
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Strips.FamilyFlattening







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




theorem exists_terminal_saddle_band_flattening
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
        (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2),
      0 < r ∧ r < ε ∧ closedSquare r ⊆ e.source ∧
      0 < w ∧ 0 < η ∧ η < w ∧ η < ε ∧ (∀ i, a i < b i) ∧
      (∀ i, (F i).source = Ioo (a i - w) (b i + w) ×ˢ Ioo (-w) w) ∧
      (∀ i, ContMDiffOn IR2 (𝓡 2) ∞ (F i) (F i).source) ∧
      (∀ i, ContMDiffOn (𝓡 2) IR2 ∞ (F i).symm (F i).target) ∧
      (∀ i z, z ∈ (F i).source → h (F i z) = h p + z.2) ∧
      Pairwise (fun i j => Disjoint (F i).target (F j).target) ∧
      h ⁻¹' Icc (h p - η) (h p + η) ⊆ interior P.core ∧
      h ⁻¹' Icc (h p - η) (h p + η) ⊆ e '' openSquare r ∪
        ⋃ i, F i '' (Icc (a i) (b i) ×ˢ Icc (-η) η) ∧
      (∃ a₀ b₀ : Fin 2 → Real,
        (∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i) ∧
        (⋃ i, F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
          (h ⁻¹' {h p}) \ e '' openSquare r ∧
        ∀ i, range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
            (F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
          {F i (a₀ i, 0), F i (b₀ i, 0)}) ∧
      ((∀ i j : Fin 2 × Fin 2,
        e (contact r i) ∈ connectedComponentIn ((h ⁻¹' {h p}) \ e '' openSquare r)
          (e (contact r j)) ↔ i.1 = j.1) ∨
       (∀ i j : Fin 2 × Fin 2,
        e (contact r i) ∈ connectedComponentIn ((h ⁻¹' {h p}) \ e '' openSquare r)
          (e (contact r j)) ↔ i.2 = j.2)) ∧
      ∃ (K V : Set E3) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
        IsCompact K ∧ K ⊆ {x | |inner Real (M.v : E3) x - h p| ≤ ε} ∧
        IsOpen V ∧ g p ∈ V ∧ EqOn D id V ∧
        (∀ x ∉ K, D x = x) ∧
        (∀ x, inner Real (M.v : E3) (D x) = inner Real (M.v : E3) x) ∧
        (∀ x, inner Real (M.v : E3) x = h p → D x = x) ∧
        ∀ i t, t ∈ Icc (-η) η → ∀ s ∈ Icc (a i) (b i),
          D (g (F i (s, t))) = g (F i (s, 0)) + t • (M.v : E3) := by
  dsimp only
  let h := fun q => inner Real (M.v : E3) (g q)
  have hgemb := M.tree.embedding_of_mem_leaves hg
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real (M.v : E3)).contMDiff.comp hgemb.contMDiff
  obtain ⟨r, w, η₀, a, b, F, U, hr, hrε, hrs, hw, _, _, _, hab,
      hFs, hF, hFi, hheight, hcover, hdisjoint, hU, hUdisjoint, hFU, _, _, hends, hpair⟩ :=
    M.exists_terminal_saddle_separated_band hg P hP hcaps hp hc e he0 hep he hei hform hε
  let d := w / 4
  have hd : 0 < d := by dsimp [d]; linarith
  let a' : Fin 2 → Real := fun i => a i - d
  let b' : Fin 2 → Real := fun i => b i + d
  let B : Fin 2 → Set (Real × Real) :=
    fun i => Ioo (a' i - d) (b' i + d) ×ˢ Ioo (-d) d
  have hBopen (i : Fin 2) : IsOpen (B i) := isOpen_Ioo.prod isOpen_Ioo
  have hBF (i : Fin 2) : B i ⊆ (F i).source := by
    intro z hz
    rw [hFs i]
    dsimp [B, a', b', d] at hz ⊢
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  let G (i : Fin 2) := (F i).restrOpen (B i) (hBopen i)
  have hGs (i : Fin 2) : (G i).source = B i := by
    rw [(F i).restrOpen_source]
    exact inter_eq_right.mpr (hBF i)
  have hG (i : Fin 2) : ContMDiffOn IR2 (𝓡 2) ∞ (G i) (G i).source :=
    (hF i).mono inter_subset_left
  have hGi (i : Fin 2) : ContMDiffOn (𝓡 2) IR2 ∞ (G i).symm (G i).target :=
    (hFi i).mono inter_subset_left
  have hGheight (i : Fin 2) (z : Real × Real) (hz : z ∈ (G i).source) :
      h (G i z) = h p + z.2 := hheight i z hz.1
  have hGU (i : Fin 2) (q : S2) (hq : q ∈ (G i).target) :
      (Real ∙ (M.v : E3))ᗮ.orthogonalProjectionOnto (g q) ∈ U i := hFU i q hq.1
  have hGdisjoint : Pairwise (fun i j => Disjoint (G i).target (G j).target) :=
    fun i j hij => (hdisjoint hij).mono inter_subset_left inter_subset_left
  have hGeq : ∀ i, (G i : (Real × Real) → S2) = F i := fun _ => rfl
  have hGcover : (⋃ i, G i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real))) =
      (h ⁻¹' {h p}) \ e '' openSquare r := by
    simpa only [hGeq] using hcover
  have hGends : ∀ i, range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
      (G i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real))) =
      {G i (a i, 0), G i (b i, 0)} := by
    simpa only [hGeq] using hends
  let C (i : Fin 2) : Set (Real × Real) := Ioo (a' i) (b' i) ×ˢ Ioo (-d) d
  have hCG (i : Fin 2) : C i ⊆ (G i).source := by
    intro z hz
    rw [hGs i]
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  let O := (e '' openSquare r ∪ ⋃ i, G i '' C i) ∩ interior P.core
  have hO : IsOpen O := ((e.isOpen_image_of_subset_source (isOpen_openSquare r)
    ((openSquare_subset_closedSquare r).trans hrs)).union
      (isOpen_iUnion fun i => (G i).isOpen_image_of_subset_source
        (isOpen_Ioo.prod isOpen_Ioo) (hCG i))).inter isOpen_interior
  have hlevelO : h ⁻¹' {h p} ⊆ O := by
    intro q hq
    refine ⟨?_, M.physical_critical_level_subset_interior_core hg P hP hcaps hp hc hq⟩
    by_cases hqpatch : q ∈ e '' openSquare r
    · exact Or.inl hqpatch
    · right
      obtain ⟨i, ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩⟩ := mem_iUnion.mp
        (hcover.superset ⟨hq, hqpatch⟩)
      have ht0 : t = 0 := ht
      subst t
      apply mem_iUnion_of_mem i
      refine ⟨(s, 0), ?_, rfl⟩
      exact ⟨⟨by dsimp [a']; linarith [hs.1],
        by dsimp [b']; linarith [hs.2]⟩, ⟨by linarith, hd⟩⟩
  obtain ⟨δ, hδ, hband⟩ :=
    Poincare.Topology.exists_closedBand_subset_of_fiber_subset_open hh.continuous hO hlevelO
  let η := min δ (min d ε) / 2
  have hη : 0 < η := half_pos (lt_min hδ (lt_min hd hε))
  have hηδ : η ≤ δ := (half_le_self (le_min hδ.le (le_min hd.le hε.le))).trans
    (min_le_left _ _)
  have hηd : η < d := (half_lt_self (lt_min hδ (lt_min hd hε))).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hηε : η < ε := (half_lt_self (lt_min hδ (lt_min hd hε))).trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  have hsmall : h ⁻¹' Icc (h p - η) (h p + η) ⊆ O := by
    intro q hq
    apply hband
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
  obtain ⟨K, hK, hKsubset, D, hDh, hDcentral, hDfix, hflat, V, hV, hpV, hDV⟩ :=
    exists_supported_ambient_strip_family_flattening hgemb
      (mem_sphere_zero_iff_norm.mp M.v.property) p a' b' G hd hη hηd (lt_min hηd hηε)
      hGs hG hGi hGheight U (fun i => (hU i).1) hUdisjoint
      (fun i => (hU i).2) hGU
  refine ⟨r, d, η, a', b', G, hr, hrε, hrs, hd, hη, hηd, hηε,
    (fun i => by dsimp [a', b']; linarith [hab i]), hGs, hG, hGi, hGheight,
    hGdisjoint, (fun q hq => (hsmall hq).2), ?_,
    ⟨a, b, (fun i => ⟨by dsimp [a']; linarith, hab i,
      by dsimp [b']; linarith⟩), hGcover, hGends⟩, hpair,
    K, V, D, hK, (fun x hx => (hKsubset hx).1.trans (min_le_right _ _)),
    hV, hpV, hDV, hDfix, hDh, hDcentral, hflat⟩
  intro q hq
  rcases (hsmall hq).1 with hpatch | hstrips
  · exact Or.inl hpatch
  · right
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hstrips
    refine mem_iUnion_of_mem i ⟨z, ⟨Ioo_subset_Icc_self hz.1, ?_⟩, rfl⟩
    have hhgt := hGheight i z (hCG i hz)
    exact ⟨by linarith [hq.1], by linarith [hq.2]⟩

end Poincare.Manifold.Schoenflies.SphereMorseReduction

end

end M38Schoenflies
