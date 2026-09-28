import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Orientation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.NestedSlab

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_terminal_common_planar_neighborhood_within
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    {ρ : Real} (hρ : 0 < ρ) (hsource : closedSquare ρ ⊆ e.source)
    (hρmatch : 2 * ρ < Real.sqrt d.scale * d.matchingRadius)
    (V : Set E2) (hV : IsOpen V)
    (hcritical : ∀ x ∈ closedSquare ρ,
      (d.flatten (g (e x))) 2 = inner Real (M.v : E3) (g p) →
        Saddle.toE2 (d.flatten (g (e x))) ∈ V) :
    ∃ δ : Real, 0 < δ ∧
      ∃ N : Set E2, IsOpen N ∧ IsCompact (closure N) ∧ closure N ⊆ V ∧
        (∀ z ∈ Icc (inner Real (M.v : E3) (g p) - δ)
          (inner Real (M.v : E3) (g p) + δ), d.A z ∩ closure N = d.B z ∩ closure N) ∧
        (∀ x ∈ closedSquare ρ,
          (d.flatten (g (e x))) 2 ∈ Icc (inner Real (M.v : E3) (g p) - δ)
            (inner Real (M.v : E3) (g p) + δ) →
          Saddle.toE2 (d.flatten (g (e x))) ∈ N) := by
  have hge := M.tree.embedding_of_mem_leaves hg
  let c := inner Real (M.v : E3) (g p)
  obtain ⟨U, hU, hQU, hcommon⟩ := Saddle.Nested.exists_common_neighborhood_of_matching
    hge.contMDiff.continuous hge.isEmbedding.injective d.filledModel d.flatten d.scale_pos hρ.le
    hρmatch d.matching_source d.matching_actual_source d.matching
  let Q : Set E3 := (fun x => d.flatten (g (e x))) '' closedSquare ρ
  have hQ : IsCompact Q := (isCompact_closedSquare hρ.le).image_of_continuousOn
    (d.flatten.continuous.comp_continuousOn
      (hge.contMDiff.continuous.comp_continuousOn (e.continuousOn.mono hsource)))
  have hz : Continuous (fun y : E3 => y 2) :=
    (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).continuous
  have hproj : Continuous Saddle.toE2 := by
    apply ContDiff.continuous (n := ∞) (𝕜 := Real)
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff
  have hlift : Continuous (fun z : Real × E2 => Saddle.toE3 z.2 z.1) := by
    apply ContDiff.continuous (n := ∞) (𝕜 := Real)
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff.comp contDiff_snd
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff.comp contDiff_snd
    · exact contDiff_fst
  let C := Saddle.toE2 '' (Q ∩ {y : E3 | y 2 = c})
  have hC : IsCompact C := (hQ.inter_right (isClosed_eq hz continuous_const)).image hproj
  let O : Set E2 := (fun x => Saddle.toE3 x c) ⁻¹' U
  have hO : IsOpen O := hU.preimage
    (hlift.comp (continuous_const.prodMk continuous_id))
  have hCO : C ⊆ O := by
    rintro _ ⟨y, ⟨hyQ, hyc⟩, rfl⟩
    change Saddle.toE3 (Saddle.toE2 y) c ∈ U
    have heq : Saddle.toE3 (Saddle.toE2 y) c = y := by
      ext i
      fin_cases i <;> simp_all [Saddle.toE2, Saddle.toE3]
    rw [heq]
    exact hQU hyQ
  have hCV : C ⊆ V := by
    rintro _ ⟨y, ⟨⟨x, hx, rfl⟩, hyc⟩, rfl⟩
    exact hcritical x hx hyc
  obtain ⟨N, hN, hCN, hNOV, hNc⟩ :=
    exists_open_between_and_isCompact_closure hC (hO.inter hV) (subset_inter hCO hCV)
  have hNO : closure N ⊆ O := hNOV.trans inter_subset_left
  have hNV : closure N ⊆ V := hNOV.trans inter_subset_right
  obtain ⟨T, Z, hT, _, hcT, hNZ, hTZ⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({c} : Set Real)) hNc (hU.preimage hlift)
    (by rintro ⟨t, x⟩ ⟨ht, hx⟩; have ht' : t = c := ht; subst t; exact hNO hx)
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds (hcT rfl))
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  obtain ⟨a, ha, hband⟩ := Poincare.Topology.exists_closedBand_subset_of_fiber_subset_open
    (h := fun q : Q => (q : E3) 2) (hz.comp continuous_subtype_val)
    (hN.preimage (hproj.comp continuous_subtype_val)) (c := c)
    (by intro y hy; exact hCN ⟨y, ⟨y.property, hy⟩, rfl⟩)
  let δ := min a (ε / 2)
  have hδ : 0 < δ := lt_min ha (half_pos hε)
  refine ⟨δ, hδ, N, hN, hNc, hNV, ?_, ?_⟩
  · intro z hzc
    have hinside (x : E2) (hx : x ∈ closure N) : Saddle.toE3 x z ∈ U := by
      apply hTZ (a := (z, x)) ⟨hεT ?_, hNZ hx⟩
      rw [mem_ball, Real.dist_eq]
      apply abs_lt.mpr
      have := min_le_right a (ε / 2)
      change c - δ ≤ z ∧ z ≤ c + δ at hzc
      constructor <;> dsimp [δ] at * <;> linarith [hzc.1, hzc.2]
    ext x
    constructor
    · rintro ⟨hx, hxN⟩
      have hm : Saddle.toE3 x z ∈ (d.flatten '' range g) ∩ U := ⟨hx, hinside x hxN⟩
      rw [hcommon] at hm
      exact ⟨by simpa only [TerminalSaddleGeometry.B, Diffeomorph.coe_trans,
        image_comp, mem_ofPred_eq] using hm.1, hxN⟩
    · rintro ⟨hx, hxN⟩
      have hm : Saddle.toE3 x z ∈ ((d.filledModel.trans d.flatten) '' sphere (0 : E3) 1) ∩ U :=
        ⟨by simpa only [TerminalSaddleGeometry.B, Diffeomorph.coe_trans,
          image_comp, mem_ofPred_eq] using hx, hinside x hxN⟩
      rw [← hcommon] at hm
      exact ⟨hm.1, hxN⟩
  · intro x hx hz'
    apply hband (a := ⟨d.flatten (g (e x)), mem_image_of_mem _ hx⟩)
    have := min_le_left a (ε / 2)
    change c - δ ≤ _ ∧ _ ≤ c + δ at hz'
    constructor <;> dsimp [δ] at * <;> linarith [hz'.1, hz'.2]

theorem exists_terminal_common_planar_neighborhood_for_square
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    {ρ : Real} (hρ : 0 < ρ) (hsource : closedSquare ρ ⊆ e.source)
    (hρmatch : 2 * ρ < Real.sqrt d.scale * d.matchingRadius) :
    ∃ δ : Real, 0 < δ ∧
      ∃ N : Set E2, IsOpen N ∧ IsCompact (closure N) ∧
        (∀ z ∈ Icc (inner Real (M.v : E3) (g p) - δ)
          (inner Real (M.v : E3) (g p) + δ), d.A z ∩ closure N = d.B z ∩ closure N) ∧
        (∀ x ∈ closedSquare ρ,
          (d.flatten (g (e x))) 2 ∈ Icc (inner Real (M.v : E3) (g p) - δ)
            (inner Real (M.v : E3) (g p) + δ) →
          Saddle.toE2 (d.flatten (g (e x))) ∈ N) := by
  obtain ⟨δ, hδ, N, hN, hNc, _, hcommon, hpatch⟩ :=
    exists_terminal_common_planar_neighborhood_within hg d hρ hsource hρmatch univ
      isOpen_univ (fun _ _ _ => mem_univ _)
  exact ⟨δ, hδ, N, hN, hNc, hcommon, hpatch⟩

theorem exists_terminal_common_planar_neighborhood
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e) :
    ∃ ρ δ : Real, 0 < ρ ∧ 0 < δ ∧
      closedSquare ρ ⊆ e.source ∧
      ∃ N : Set E2, IsOpen N ∧ IsCompact (closure N) ∧
        (∀ z ∈ Icc (inner Real (M.v : E3) (g p) - δ)
          (inner Real (M.v : E3) (g p) + δ), d.A z ∩ closure N = d.B z ∩ closure N) ∧
        (∀ x ∈ closedSquare ρ,
          (d.flatten (g (e x))) 2 ∈ Icc (inner Real (M.v : E3) (g p) - δ)
            (inner Real (M.v : E3) (g p) + δ) →
          Saddle.toE2 (d.flatten (g (e x))) ∈ N) := by
  let ρ := min d.r (Real.sqrt d.scale * d.matchingRadius) / 4
  have hsqrt : 0 < Real.sqrt d.scale := Real.sqrt_pos.mpr d.scale_pos
  have hρ : 0 < ρ := div_pos (lt_min d.r_pos (mul_pos hsqrt d.matchingRadius_pos))
    (by norm_num)
  have hρr : ρ ≤ d.r := by
    have := min_le_left d.r (Real.sqrt d.scale * d.matchingRadius)
    dsimp [ρ] at hρ ⊢
    linarith
  have hρmatch : 2 * ρ < Real.sqrt d.scale * d.matchingRadius := by
    have := min_le_right d.r (Real.sqrt d.scale * d.matchingRadius)
    dsimp [ρ] at hρ ⊢
    linarith
  have hsource : closedSquare ρ ⊆ e.source := by
    intro x hx
    exact d.square_source ⟨hx.1.trans hρr, hx.2.trans hρr⟩
  obtain ⟨δ, hδ, N, hN⟩ :=
    exists_terminal_common_planar_neighborhood_for_square hg d hρ hsource hρmatch
  exact ⟨ρ, δ, hρ, hδ, hsource, N, hN⟩

theorem exists_terminal_common_planar_neighborhood_of_morse_chart
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ ρ δ : Real, 0 < ρ ∧ 0 < δ ∧
      closedSquare ρ ⊆ e.source ∧
      ∃ N : Set E2, IsOpen N ∧ IsCompact (closure N) ∧
        (∀ z ∈ Icc (inner Real (M.v : E3) (g p) - δ)
          (inner Real (M.v : E3) (g p) + δ), d.A z ∩ closure N = d.B z ∩ closure N) ∧
        (fun x => Saddle.toE2 (d.flatten (g (e x)))) '' closedSquare ρ ⊆ N := by
  obtain ⟨r, δ, hr, hδ, hsource, N, hN, hNc, hcommon, hpatch⟩ :=
    exists_terminal_common_planar_neighborhood hg d
  let ρ := min r (Real.sqrt δ) / 2
  have hroot : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  have hρ : 0 < ρ := half_pos (lt_min hr hroot)
  have hρr : ρ ≤ r := by
    have := min_le_left r (Real.sqrt δ)
    dsimp [ρ] at hρ ⊢
    linarith
  have hρδ : ρ ^ 2 < δ := by
    have := min_le_right r (Real.sqrt δ)
    have := Real.sq_sqrt hδ.le
    dsimp [ρ] at hρ ⊢
    nlinarith
  have hsub : closedSquare ρ ⊆ closedSquare r :=
    fun x hx => ⟨hx.1.trans hρr, hx.2.trans hρr⟩
  refine ⟨ρ, δ, hρ, hδ, hsub.trans hsource, N, hN, hNc, hcommon, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  apply hpatch x (hsub hx)
  have hh : (d.flatten (g (e x))) 2 =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2 := by
    change d.frame (d.D (g (e x))) 2 = _
    rw [d.frame_height, d.D_height, hform x (hsource (hsub hx))]
  rw [hh]
  have hx0 := abs_le.mp hx.1
  have hx1 := abs_le.mp hx.2
  have hsq0 : (x 0)^2 ≤ ρ^2 := sq_le_sq.mpr (by simpa [abs_of_pos hρ] using hx.1)
  have hsq1 : (x 1)^2 ≤ ρ^2 := sq_le_sq.mpr (by simpa [abs_of_pos hρ] using hx.2)
  constructor <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
