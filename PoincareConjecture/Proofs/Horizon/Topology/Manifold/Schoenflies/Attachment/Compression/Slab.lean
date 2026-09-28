import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Push.Local
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Rounding.Push.Cutoff











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Rounding

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [TopologicalSpace M]

omit [NormedSpace Real E] [FiniteDimensional Real E] in
private theorem exists_uniform_slab_height
    (q : E × Real → M) (hq : Continuous q) {L : Set E} (hL : IsCompact L)
    {W : Set M} (hW : IsOpen W) (hzero : ∀ x ∈ L, q (x, 0) ∈ W) :
    ∃ δ : Real, 0 < δ ∧ δ < 1 ∧
      ∀ x ∈ L, ∀ t ∈ Icc (0 : Real) δ, q (x, t) ∈ W := by
  have hLW : L ×ˢ {0} ⊆ q ⁻¹' W := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact hzero x hx
  obtain ⟨U, V, _, hV, hLU, h0V, hUV⟩ :=
    generalized_tube_lemma hL isCompact_singleton (hW.preimage hq) hLW
  obtain ⟨r, hr, hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hV.mem_nhds (h0V (mem_singleton 0)))
  refine ⟨min r (1 / 2), lt_min hr (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro x hx t ht
  apply hUV
  refine ⟨hLU hx, hrV ?_⟩
  rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact ht.2.trans (min_le_left _ _)

private def verticalShift :
    Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real) (E × Real) (E × Real) ∞ where
  toFun p := (p.1, p.2 + 1)
  invFun p := (p.1, p.2 - 1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  contMDiff_toFun := (contDiff_fst.prodMk (contDiff_snd.add contDiff_const)).contMDiff
  contMDiff_invFun := (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)).contMDiff

variable {H A : Type*} [NormedAddCommGroup A] [NormedSpace Real A]
  [TopologicalSpace H] [ChartedSpace H M] [T2Space M]
  {I : ModelWithCorners Real A H}



theorem exists_slab_compression_with_graph
    (C : Opens M) (e : Diffeomorph I 𝓘(Real, E × Real) C (E × Real) ∞)
    {B D W O : Set M} (hB : IsCompact B) (hW : IsOpen W) (hO : IsOpen O)
    (hslab : B ∩ C = (fun p => (e.symm p : M)) ''
      {p : E × Real | 0 ≤ p.2 ∧ p.2 ≤ 1})
    (hzero : D ∩ C = (fun p => (e.symm p : M)) '' {p : E × Real | p.2 = 0})
    (hedge : B \ C ⊆ D) (hDW : D ⊆ W) (hBO : B ⊆ O) :
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
  let q : E × Real → M := fun p => (e.symm p : M)
  have hq : Continuous q := continuous_subtype_val.comp e.symm.continuous
  have hqinj : Function.Injective q := Subtype.val_injective.comp e.symm.injective
  have hqB (p : E × Real) (hp : 0 ≤ p.2 ∧ p.2 ≤ 1) : q p ∈ B :=
    (show q p ∈ B ∩ C from hslab.symm ▸ mem_image_of_mem q hp).1
  have hqD (x : E) : q (x, 0) ∈ D :=
    (show q (x, 0) ∈ D ∩ C from
      hzero.symm ▸ mem_image_of_mem q (show (x, (0 : Real)).2 = 0 from rfl)).1
  obtain ⟨χ, hχ, hχc, hχrange, _, hχone, _⟩ :=
    exists_slab_cutoff C e.toHomeomorph hB hW hslab (hedge.trans hDW)
  obtain ⟨δ, hδ, hδ1, hsmall⟩ :=
    exists_uniform_slab_height q hq hχc hW (fun x _ => hDW (hqD x))
  let a : E → Real := fun x => (δ - 1) * χ x
  have ha : ContDiff Real ∞ a := contDiff_const.mul hχ
  have hac : HasCompactSupport a := hχc.mul_left
  have harange (x : E) : δ - 1 ≤ a x ∧ a x ≤ 0 := by
    have hx := hχrange x
    dsimp [a]
    constructor
    · simpa only [mul_one] using
        mul_le_mul_of_nonpos_left hx.2 (sub_nonpos.mpr hδ1.le)
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hδ1.le) hx.1
  let e' := e.trans (verticalShift (E := E)).symm
  let q' : E × Real → M := fun p => (e'.symm p : M)
  have hq' (p : E × Real) : q' p = q (p.1, p.2 + 1) := rfl
  have hq'cont : Continuous q' := continuous_subtype_val.comp e'.symm.continuous
  let U : Set (E × Real) := q' ⁻¹' O ∩ {p | 0 < p.2 + 1}
  have hU : IsOpen U := (hO.preimage hq'cont).inter
    (isOpen_lt continuous_const (continuous_snd.add continuous_const))
  have htrace (x : E) (_ : x ∈ tsupport a) (t : Real) (ht : t ∈ Icc (0 : Real) 1) :
      (x, t * a x) ∈ U := by
    have hx := harange x
    have hlow : δ ≤ t * a x + 1 := by
      have hh := mul_le_mul_of_nonpos_right ht.2 hx.2
      linarith [hx.1]
    have hupp : t * a x + 1 ≤ 1 := by
      linarith [mul_nonpos_of_nonneg_of_nonpos ht.1 hx.2]
    exact ⟨hBO (hqB _ ⟨hδ.le.trans hlow, hupp⟩), hδ.trans_le hlow⟩
  obtain ⟨K₀, hK₀, hK₀U, G, hGfirst, hGfix, hGtop, _⟩ :=
    exists_graph_push_within a ha hac hU htrace
  have hGbottom (x : E) : G (x, -1) = (x, -1) := by
    apply hGfix
    intro hx
    have hpos := (hK₀U hx).2
    norm_num at hpos
  have hmono (x : E) : Monotone (fun z : Real => (G (x, z)).2) :=
    (strictMono_vertical_of_compact_support G.toHomeomorph hGfirst hK₀ hGfix x).monotone
  let K : Set M := q' '' K₀
  have hK : IsCompact K := hK₀.image hq'cont
  have hKO : K ⊆ O := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hK₀U hp).1
  have hKC : K ⊆ C := by
    rintro _ ⟨p, _, rfl⟩
    exact (e'.symm p).property
  have hKD : Disjoint K D := by
    apply disjoint_left.mpr
    rintro y ⟨p, hp, rfl⟩ hy
    obtain ⟨z, hz, he⟩ :=
      (show q' p ∈ q '' {p : E × Real | p.2 = 0} from
        hzero ▸ ⟨hy, (e'.symm p).property⟩)
    have he' : z = (p.1, p.2 + 1) := hqinj he
    have hheight : p.2 + 1 = 0 := by
      change z.2 = 0 at hz
      simpa only [he'] using hz
    exact (ne_of_gt (hK₀U hp).2) hheight
  let f : Diffeomorph I I C C ∞ := (e'.trans G).trans e'.symm
  have hffix (x : C) (hx : (x : M) ∉ K) : f x = x := by
    have hn : e' x ∉ K₀ := by
      intro hp
      exact hx ⟨e' x, hp, by simp [q']⟩
    change e'.symm (G (e' x)) = x
    rw [hGfix _ hn, e'.symm_apply_apply]
  obtain ⟨F, hF, hFfix⟩ :=
    Diffeomorph.exists_extension_of_isCompact C f hK hKC hffix
  have hcoord (p : E × Real) : F (q' p) = q' (G p) := by
    rw [hF]
    change (e'.symm (G (e' (e'.symm p))) : M) = (e'.symm (G p) : M)
    rw [e'.apply_symm_apply]
  let G' := ((verticalShift (E := E)).symm.trans G).trans (verticalShift (E := E))
  have hG' (p : E × Real) :
      G' p = ((G (p.1, p.2 - 1)).1, (G (p.1, p.2 - 1)).2 + 1) := rfl
  have hG'first (p : E × Real) : (G' p).1 = p.1 := by
    change (G (p.1, p.2 - 1)).1 = p.1
    exact hGfirst _
  have hG'zero (x : E) : G' (x, 0) = (x, 0) := by
    rw [hG']
    simp only [zero_sub, hGbottom, neg_add_cancel]
  have hG'top (x : E) : G' (x, 1) = (x, 1 + a x) := by
    rw [hG']
    simp only [sub_self, hGtop, add_comm]
  have hcoord' (p : E × Real) : F (q p) = q (G' p) := by
    have hqr : q' (p.1, p.2 - 1) = q p := by simp [hq']
    calc
      F (q p) = F (q' (p.1, p.2 - 1)) := congrArg F hqr.symm
      _ = q' (G (p.1, p.2 - 1)) := hcoord _
      _ = q (G' p) := rfl
  have harange' (x : E) : -1 < a x ∧ a x ≤ 0 :=
    ⟨by linarith [(harange x).1], (harange x).2⟩
  refine ⟨a, ha, hac, harange', K, hK, hKO, hKD, F, hFfix, ?_,
    G', hG'first, hG'zero, hG'top, hcoord'⟩
  rintro _ ⟨y, hy, rfl⟩
  by_cases hyC : y ∈ C
  · obtain ⟨p, hp, rfl⟩ := (show y ∈ q '' {p : E × Real | 0 ≤ p.2 ∧ p.2 ≤ 1}
        from hslab ▸ ⟨hy, hyC⟩)
    let r : E × Real := (p.1, p.2 - 1)
    have hqr : q' r = q p := by simp [hq', r]
    rw [← hqr, hcoord, hq', hGfirst]
    have hlo := hmono p.1 (show (-1 : Real) ≤ p.2 - 1 by linarith [hp.1])
    have hhi := hmono p.1 (show p.2 - 1 ≤ 0 by linarith [hp.2])
    change (G (p.1, -1)).2 ≤ (G r).2 at hlo
    change (G r).2 ≤ (G (p.1, 0)).2 at hhi
    rw [hGbottom] at hlo
    rw [hGtop] at hhi
    change -1 ≤ (G r).2 at hlo
    change (G r).2 ≤ a p.1 at hhi
    have hheight : 0 ≤ (G r).2 + 1 ∧ (G r).2 + 1 ≤ 1 := by
      have hh := (harange p.1).2
      constructor <;> linarith
    have hmem := hqB (p.1, (G r).2 + 1) hheight
    refine ⟨hmem, ?_⟩
    by_cases hχp : χ p.1 = 1
    · have hsupport : p.1 ∈ tsupport χ := subset_tsupport χ (by simp [hχp])
      apply hsmall p.1 hsupport _ ⟨hheight.1, ?_⟩
      dsimp [a] at hhi
      rw [hχp] at hhi
      linarith
    · by_contra hn
      exact hχp (hχone (p.1, (G r).2 + 1) ⟨hmem, hn⟩)
  · rw [hFfix y (fun hk => hyC (hKC hk))]
    exact ⟨hy, hDW (hedge ⟨hy, hyC⟩)⟩



theorem exists_slab_compression
    (C : Opens M) (e : Diffeomorph I 𝓘(Real, E × Real) C (E × Real) ∞)
    {B D W O : Set M} (hB : IsCompact B) (hW : IsOpen W) (hO : IsOpen O)
    (hslab : B ∩ C = (fun p => (e.symm p : M)) ''
      {p : E × Real | 0 ≤ p.2 ∧ p.2 ≤ 1})
    (hzero : D ∩ C = (fun p => (e.symm p : M)) '' {p : E × Real | p.2 = 0})
    (hedge : B \ C ⊆ D) (hDW : D ⊆ W) (hBO : B ⊆ O) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ O ∧ Disjoint K D ∧
      ∃ F : Diffeomorph I I M M ∞,
        (∀ x ∉ K, F x = x) ∧ F '' B ⊆ B ∩ W := by
  obtain ⟨_, _, _, _, K, hK, hKO, hKD, F, hfix, himage, _⟩ :=
    exists_slab_compression_with_graph C e hB hW hO hslab hzero hedge hDW hBO
  exact ⟨K, hK, hKO, hKD, F, hfix, himage⟩

end Poincare.Manifold.Schoenflies.Rounding
