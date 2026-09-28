import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Compression.Slab
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Compression.GraphFamily
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Compression.FamilyExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Compression

open Rounding

private abbrev E2 := EuclideanSpace Real (Fin 2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]

private def familyVerticalShift :
    Diffeomorph 𝓘(Real, E × Real) 𝓘(Real, E × Real) (E × Real) (E × Real) ∞ where
  toFun p := (p.1, p.2 + 1)
  invFun p := (p.1, p.2 - 1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  contMDiff_toFun := (contDiff_fst.prodMk (contDiff_snd.add contDiff_const)).contMDiff
  contMDiff_invFun := (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)).contMDiff

theorem exists_slab_compression_family_with_relative_support
    (C : Opens E2) (e : Diffeomorph (𝓡 2) 𝓘(Real, E × Real) C (E × Real) ∞)
    {B D W O : Set E2} (hB : IsCompact B) (hW : IsOpen W) (hO : IsOpen O)
    (hslab : B ∩ C = (fun p => (e.symm p : E2)) ''
      {p : E × Real | 0 ≤ p.2 ∧ p.2 ≤ 1})
    (hzero : D ∩ C = (fun p => (e.symm p : E2)) '' {p : E × Real | p.2 = 0})
    (hedge : B \ C ⊆ D) (hDW : D ⊆ W) (hBO : B \ D ⊆ O) :
    ∃ K : Set E2, IsCompact K ∧ K ⊆ O ∧ Disjoint K D ∧
      ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Phi 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Phi t x = x) ∧ Phi 1 '' B ⊆ B ∩ W := by
  let q : E × Real → E2 := fun p => (e.symm p : E2)
  have hq : Continuous q := continuous_subtype_val.comp e.symm.continuous
  have hqinj : Function.Injective q := Subtype.val_injective.comp e.symm.injective
  have hqB (p : E × Real) (hp : 0 ≤ p.2 ∧ p.2 ≤ 1) : q p ∈ B :=
    (show q p ∈ B ∩ C from hslab.symm ▸ mem_image_of_mem q hp).1
  have hqD (x : E) : q (x, 0) ∈ D :=
    (show q (x, 0) ∈ D ∩ C from
      hzero.symm ▸ mem_image_of_mem q (show (x, (0 : Real)).2 = 0 from rfl)).1
  have hqnotD (p : E × Real) (hp : 0 < p.2) : q p ∉ D := by
    intro h
    obtain ⟨z, hz, he⟩ :=
      (show q p ∈ q '' {p : E × Real | p.2 = 0} from
        hzero ▸ ⟨h, (e.symm p).property⟩)
    have he' := hqinj he
    exact (ne_of_gt hp) (he' ▸ hz)
  obtain ⟨χ, hχ, hχc, hχrange, _, hχone, _⟩ :=
    exists_slab_cutoff C e.toHomeomorph hB hW hslab (hedge.trans hDW)
  have hLW : tsupport χ ×ˢ {0} ⊆ q ⁻¹' W := by
    rintro ⟨x, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact hDW (hqD x)
  obtain ⟨U, V, _, hV, hLU, h0V, hUV⟩ :=
    generalized_tube_lemma hχc isCompact_singleton (hW.preimage hq) hLW
  obtain ⟨r, hr, hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hV.mem_nhds (h0V (mem_singleton 0)))
  let δ : Real := min r (1 / 2)
  have hδ : 0 < δ := lt_min hr (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hsmall (x : E) (hx : x ∈ tsupport χ) (t : Real) (ht : t ∈ Icc 0 δ) :
      q (x, t) ∈ W := by
    apply hUV
    refine ⟨hLU hx, hrV ?_⟩
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2.trans (min_le_left _ _)
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
  let e' := e.trans (familyVerticalShift (E := E)).symm
  let q' : E × Real → E2 := fun p => (e'.symm p : E2)
  have hq' (p : E × Real) : q' p = q (p.1, p.2 + 1) := rfl
  have hq'cont : Continuous q' := continuous_subtype_val.comp e'.symm.continuous
  let O' : Set (E × Real) := q' ⁻¹' O ∩ {p | 0 < p.2 + 1}
  have hO' : IsOpen O' := (hO.preimage hq'cont).inter
    (isOpen_lt continuous_const (continuous_snd.add continuous_const))
  have htrace (x : E) (_ : x ∈ tsupport a) (t : Real) (ht : t ∈ Icc (0 : Real) 1) :
      (x, t * a x) ∈ O' := by
    have hx := harange x
    have hlow : δ ≤ t * a x + 1 := by
      have hh := mul_le_mul_of_nonpos_right ht.2 hx.2
      linarith [hx.1]
    have hupp : t * a x + 1 ≤ 1 := by
      linarith [mul_nonpos_of_nonneg_of_nonpos ht.1 hx.2]
    have hpos := hδ.trans_le hlow
    exact ⟨hBO ⟨hqB _ ⟨hpos.le, hupp⟩, hqnotD _ hpos⟩, hpos⟩
  obtain ⟨K₀, hK₀, hK₀O, G, hG0, hGs, hGfirst, hGfix, hGtop⟩ :=
    exists_graph_push_family_within a ha hac hO' htrace
  have hGbottom (x : E) : G 1 (x, -1) = (x, -1) := by
    apply hGfix
    intro hx
    have hpos := (hK₀O hx).2
    norm_num at hpos
  have hmono (x : E) : Monotone (fun z : Real => (G 1 (x, z)).2) :=
    (strictMono_vertical_of_compact_support (G 1).toHomeomorph
      (hGfirst 1) hK₀ (hGfix 1) x).monotone
  let K : Set E2 := q' '' K₀
  have hK : IsCompact K := hK₀.image hq'cont
  have hKO : K ⊆ O := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hK₀O hp).1
  have hKC : K ⊆ C := by
    rintro _ ⟨p, _, rfl⟩
    exact (e'.symm p).property
  have hKD : Disjoint K D := by
    apply disjoint_left.mpr
    rintro y ⟨p, hp, rfl⟩ hy
    exact hqnotD (p.1, p.2 + 1) (hK₀O hp).2 hy
  let f (t : Real) : Diffeomorph (𝓡 2) (𝓡 2) C C ∞ := (e'.trans (G t)).trans e'.symm
  have hffix (t : Real) (x : C) (hx : (x : E2) ∉ K) : f t x = x := by
    have hn : e' x ∉ K₀ := by
      intro hp
      exact hx ⟨e' x, hp, by simp [q']⟩
    change e'.symm (G t (e' x)) = x
    rw [hGfix t _ hn, e'.symm_apply_apply]
  have hGm : ContMDiff (𝓘(Real, Real).prod 𝓘(Real, E × Real)) 𝓘(Real, E × Real) ∞
      (fun z : Real × (E × Real) => G z.1 z.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hGs.contMDiff
  have hfs : ContMDiff (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞
      (fun z : Real × C => f z.1 z.2) :=
    e'.symm.contMDiff.comp
      (hGm.comp (contMDiff_fst.prodMk (e'.contMDiff.comp contMDiff_snd)))
  obtain ⟨Phi, hPhis, hPhii, hPhi, hPhifix⟩ :=
    exists_supported_family_extension C f hfs hK hKC hffix
  have hPhi0 (x : E2) : Phi 0 x = x := by
    by_cases hx : x ∈ C
    · have h := hPhi 0 ⟨x, hx⟩
      change Phi 0 x = (e'.symm (G 0 (e' ⟨x, hx⟩)) : E2) at h
      simpa only [hG0, e'.symm_apply_apply] using h
    · exact hPhifix 0 x (fun h => hx (hKC h))
  have hcoord (t : Real) (p : E × Real) : Phi t (q' p) = q' (G t p) := by
    rw [hPhi]
    change (e'.symm (G t (e' (e'.symm p))) : E2) = (e'.symm (G t p) : E2)
    rw [e'.apply_symm_apply]
  refine ⟨K, hK, hKO, hKD, Phi, hPhi0, hPhis, hPhii, hPhifix, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  by_cases hyC : y ∈ C
  · obtain ⟨p, hp, rfl⟩ := (show y ∈ q '' {p : E × Real | 0 ≤ p.2 ∧ p.2 ≤ 1}
        from hslab ▸ ⟨hy, hyC⟩)
    let z : E × Real := (p.1, p.2 - 1)
    have hqr : q' z = q p := by simp [hq', z]
    rw [← hqr, hcoord, hq', hGfirst]
    have hlo := hmono p.1 (show (-1 : Real) ≤ p.2 - 1 by linarith [hp.1])
    have hhi := hmono p.1 (show p.2 - 1 ≤ 0 by linarith [hp.2])
    change (G 1 (p.1, -1)).2 ≤ (G 1 z).2 at hlo
    change (G 1 z).2 ≤ (G 1 (p.1, 0)).2 at hhi
    rw [hGbottom] at hlo
    rw [hGtop] at hhi
    change -1 ≤ (G 1 z).2 at hlo
    change (G 1 z).2 ≤ a p.1 at hhi
    have hheight : 0 ≤ (G 1 z).2 + 1 ∧ (G 1 z).2 + 1 ≤ 1 := by
      have hh := (harange p.1).2
      constructor <;> linarith
    have hmem := hqB (p.1, (G 1 z).2 + 1) hheight
    refine ⟨hmem, ?_⟩
    by_cases hχp : χ p.1 = 1
    · have hsupport : p.1 ∈ tsupport χ := subset_tsupport χ (by simp [hχp])
      apply hsmall p.1 hsupport _ ⟨hheight.1, ?_⟩
      dsimp [a] at hhi
      rw [hχp] at hhi
      linarith
    · by_contra hn
      exact hχp (hχone (p.1, (G 1 z).2 + 1) ⟨hmem, hn⟩)
  · rw [hPhifix 1 y (fun hk => hyC (hKC hk))]
    exact ⟨hy, hDW (hedge ⟨hy, hyC⟩)⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Compression
