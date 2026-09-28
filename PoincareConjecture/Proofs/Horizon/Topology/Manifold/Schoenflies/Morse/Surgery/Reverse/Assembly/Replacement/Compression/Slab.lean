import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Compression.Slab
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Push

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Rounding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H A M : Type*} [NormedAddCommGroup A] [NormedSpace Real A]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners Real A H}

theorem exists_slab_compression_away_disk_with_graph
    (C : Opens M) (e : Diffeomorph I 𝓘(Real, E × Real) C (E × Real) ∞)
    {B D W O : Set M} (hB : IsCompact B) (hW : IsOpen W) (hO : IsOpen O)
    (hslab : B ∩ C = (fun p => (e.symm p : M)) ''
      {p : E × Real | 0 ≤ p.2 ∧ p.2 ≤ 1})
    (hzero : D ∩ C = (fun p => (e.symm p : M)) '' {p : E × Real | p.2 = 0})
    (hedge : B \ C ⊆ D) (hDW : D ⊆ W) (hBO : B \ D ⊆ O) :
    ∃ a : E → Real, ContDiff Real ∞ a ∧ HasCompactSupport a ∧
      (∀ x, -1 < a x ∧ a x ≤ 0) ∧
      ∃ K : Set M, IsCompact K ∧ K ⊆ O ∧ Disjoint K D ∧
        ∃ F : Diffeomorph I I M M ∞,
          (∀ x ∉ K, F x = x) ∧ F '' B ⊆ B ∩ W ∧
          ∃ G : Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real)
              (E × Real) (E × Real) ∞,
            (∀ p, (G p).1 = p.1) ∧
            (∀ x, G (x, 0) = (x, 0)) ∧
            (∀ x, G (x, 1) = (x, 1 + a x)) ∧
            (∀ p, F (e.symm p : M) = (e.symm (G p) : M)) := by
  obtain ⟨a, ha, hac, harange, _, _, _, _, F₀, _, hF₀image,
      G₀, hG₀first, hG₀zero, hG₀top, hcoord₀⟩ :=
    exists_slab_compression_with_graph C e hB hW isOpen_univ
      hslab hzero hedge hDW (subset_univ B)
  let q : E × Real → M := fun p => (e.symm p : M)
  have hq : Continuous q := continuous_subtype_val.comp e.symm.continuous
  have hqinj : Function.Injective q := Subtype.val_injective.comp e.symm.injective
  have hqB (p : E × Real) (hp : 0 ≤ p.2 ∧ p.2 ≤ 1) : q p ∈ B :=
    (show q p ∈ B ∩ C from hslab.symm ▸ mem_image_of_mem q hp).1
  have hqnotD (p : E × Real) (hp : 0 < p.2) : q p ∉ D := by
    intro hD
    obtain ⟨z, hz, he⟩ :=
      (show q p ∈ q '' {p : E × Real | p.2 = 0} from
        hzero ▸ ⟨hD, (e.symm p).property⟩)
    have hep : z = p := hqinj he
    subst z
    exact hp.ne' hz
  have hthin (x : E) (t : Real) (ht : t ∈ Icc 0 (1 + a x)) :
      q (x, t) ∈ B ∩ W := by
    have hc : Continuous (fun r : Real => (G₀ (x, r)).2) := by fun_prop
    have hends : t ∈ Icc (G₀ (x, 0)).2 (G₀ (x, 1)).2 := by
      simpa only [hG₀zero, hG₀top] using ht
    obtain ⟨r, hr, he⟩ := intermediate_value_Icc (by norm_num : (0 : Real) ≤ 1)
      hc.continuousOn hends
    have hGr : G₀ (x, r) = (x, t) := Prod.ext (hG₀first (x, r)) he
    have hi := hF₀image (mem_image_of_mem F₀ (hqB (x, r) hr))
    rw [hcoord₀, hGr] at hi
    exact hi
  let U : Set (E × Real) := q ⁻¹' O ∩ {p | 0 < p.2}
  have hU : IsOpen U := (hO.preimage hq).inter
    (isOpen_lt continuous_const continuous_snd)
  have htrace (x : E) (_ : x ∈ tsupport a) (t : Real) (ht : t ∈ Icc (0 : Real) 1) :
      (x, 1 + t * a x) ∈ U := by
    have hx := harange x
    have hlow : 0 < 1 + t * a x := by
      have hh := mul_le_mul_of_nonpos_right ht.2 hx.2
      linarith
    have hupp : 1 + t * a x ≤ 1 := by
      linarith [mul_nonpos_of_nonneg_of_nonpos ht.1 hx.2]
    exact ⟨hBO ⟨hqB _ ⟨hlow.le, hupp⟩, hqnotD _ hlow⟩, hlow⟩
  obtain ⟨K₀, hK₀, hK₀U, G, hGfirst, hGfix, hGtop⟩ :=
    exists_supported_transport_between_graphs (fun _ : E => (1 : Real)) a ha hac
      continuousOn_const hU htrace
  have hGzero (x : E) : G (x, 0) = (x, 0) := by
    apply hGfix
    intro hx
    exact (lt_irrefl (0 : Real)) (hK₀U hx).2
  have hmono (x : E) : Monotone (fun z : Real => (G (x, z)).2) :=
    (strictMono_vertical_of_compact_support G.toHomeomorph hGfirst hK₀ hGfix x).monotone
  let K : Set M := q '' K₀
  have hK : IsCompact K := hK₀.image hq
  have hKO : K ⊆ O := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hK₀U hp).1
  have hKC : K ⊆ C := by
    rintro _ ⟨p, _, rfl⟩
    exact (e.symm p).property
  have hKD : Disjoint K D := by
    apply disjoint_left.mpr
    rintro _ ⟨p, hp, rfl⟩ hD
    exact hqnotD p (hK₀U hp).2 hD
  let f : Diffeomorph I I C C ∞ := (e.trans G).trans e.symm
  have hffix (x : C) (hx : (x : M) ∉ K) : f x = x := by
    have hn : e x ∉ K₀ := by
      intro hp
      exact hx ⟨e x, hp, by simp [q]⟩
    change e.symm (G (e x)) = x
    rw [hGfix _ hn, e.symm_apply_apply]
  obtain ⟨F, hF, hFfix⟩ :=
    Diffeomorph.exists_extension_of_isCompact C f hK hKC hffix
  have hcoord (p : E × Real) : F (q p) = q (G p) := by
    rw [hF]
    change (e.symm (G (e (e.symm p))) : M) = (e.symm (G p) : M)
    rw [e.apply_symm_apply]
  refine ⟨a, ha, hac, harange, K, hK, hKO, hKD, F, hFfix, ?_,
    G, hGfirst, hGzero, hGtop, hcoord⟩
  rintro _ ⟨y, hy, rfl⟩
  by_cases hyC : y ∈ C
  · obtain ⟨p, hp, rfl⟩ := (show y ∈ q '' {p : E × Real | 0 ≤ p.2 ∧ p.2 ≤ 1}
        from hslab ▸ ⟨hy, hyC⟩)
    rw [hcoord]
    have hlo := hmono p.1 hp.1
    have hhi := hmono p.1 hp.2
    change (G (p.1, 0)).2 ≤ (G p).2 at hlo
    change (G p).2 ≤ (G (p.1, 1)).2 at hhi
    rw [hGzero] at hlo
    rw [hGtop] at hhi
    have he : G p = (p.1, (G p).2) := Prod.ext (hGfirst p) rfl
    rw [he]
    exact hthin p.1 (G p).2 ⟨hlo, hhi⟩
  · rw [hFfix y (fun hk => hyC (hKC hk))]
    exact ⟨hy, hDW (hedge ⟨hy, hyC⟩)⟩

end Poincare.Manifold.Schoenflies.Rounding
