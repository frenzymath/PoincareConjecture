import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Matching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.Saddle.Resolution
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.RawMatchedCoordinates
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private def lowerSeed (σ : Real) (hσ : σ ^ 2 = 1) : S2 :=
  ⟨Saddle.vector (σ * Real.sqrt (3 / 4)) 0 (-1 / 2), by
    rw [mem_sphere_zero_iff_norm]
    have hn := EuclideanSpace.norm_sq_eq
      (Saddle.vector (σ * Real.sqrt (3 / 4)) 0 (-1 / 2))
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs,
      Saddle.vector_zero, Saddle.vector_one, Saddle.vector_two, mul_pow,
      hσ, one_mul, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 3 / 4)] at hn
    nlinarith [norm_nonneg (Saddle.vector (σ * Real.sqrt (3 / 4)) 0 (-1 / 2))]⟩

private theorem lowerSeed_height (σ : Real) (hσ : σ ^ 2 = 1) :
    Saddle.height (lowerSeed σ hσ) = -5 / 4 := by
  rw [Saddle.height_apply]
  simp only [lowerSeed, Saddle.vector_zero, Saddle.vector_two, mul_pow, hσ,
    one_mul, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 3 / 4)]
  norm_num

private def modelSeeds : Fin 3 → S2 :=
  ![lowerSeed 1 (by norm_num), lowerSeed (-1) (by norm_num),
    ⟨EuclideanSpace.single 2 1, by simp⟩]

private theorem modelSeeds_height (i : Fin 3) :
    Saddle.height (modelSeeds i) = -5 / 4 ∨ Saddle.height (modelSeeds i) = 1 := by
  fin_cases i
  · exact Or.inl (lowerSeed_height 1 (by norm_num))
  · exact Or.inl (lowerSeed_height (-1) (by norm_num))
  · right
    simp [modelSeeds, Saddle.height_apply]




theorem exists_terminal_saddle_geometry_with_matched_planar_chart
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps)
    {p : S2} (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (_hunique : ∀ q ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y => inner Real (M.v : E3) (g y)) q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source)
    (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (_het : e.target ⊆ interior P.core)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ d : TerminalSaddleGeometry M P p e, d.model = Saddle.shear ∧
      (∀ y, inner Real (M.v : E3) y = inner Real (M.v : E3) (g p) → d.D y = y) ∧
      2 * d.r < Real.sqrt d.scale * d.matchingRadius ∧
      ∃ a ε : Real, 0 < a ∧ 0 < ε ∧ 8 * d.r < a ∧ closedSquare a ⊆ e.source ∧
        ∃ R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          (∀ x ∈ closedSquare a, R x = Saddle.toE2 (d.frame (g (e x)))) ∧
          ∀ x ∈ closedSquare a, ∀ t ∈ Icc (-ε) ε,
            (Saddle.toE3 (R x) (inner Real (M.v : E3) (g p) + t) ∈ d.frame '' range g ↔
              -x 0 ^ 2 + x 1 ^ 2 = t) ∧
            (Saddle.toE3 (R x) (inner Real (M.v : E3) (g p) + t) ∈
              d.frame '' (d.filledModel '' sphere (0 : E3) 1) ↔
              -x 0 ^ 2 + x 1 ^ 2 = t) := by
  have hv : ‖(M.v : E3)‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using M.v.property
  let axis : E3 := EuclideanSpace.single 2 1
  let J : E3 ≃ₗᵢ[Real] E3 := Submodule.reflection (Real ∙ ((M.v : E3) - axis))ᗮ
  have hJv : J M.v = axis := Submodule.reflection_sub (by simp [axis, hv])
  let frame := J.toContinuousLinearEquiv.toDiffeomorph
  have hframe (y : E3) : frame y 2 = inner Real (M.v : E3) y := by
    have hinner := J.inner_map_map (M.v : E3) y
    rw [hJv] at hinner
    simpa [frame, axis, PiLp.inner_apply] using hinner
  obtain ⟨s, hs, _, _, d, hd0, hdp, hd, hdi, u, hu, hus, hactual,
      T, H, hH, hTh, _, _, _, _, hmatch⟩ :=
    Saddle.exists_filled_saddle_matching (M.tree.embedding_of_mem_leaves hg) hv p hc
      e he0 hep he hei hform zero_lt_one
  obtain ⟨a₀, ε₀, ha₀, hε₀, haSource, Q, hQ, hQlevel⟩ :=
    exists_terminal_raw_matched_morse_coordinates hg frame hframe he0 hep he hei hc hform
      (Saddle.shear.trans T) hs hu hus hactual (by
        intro x hx
        change T (Saddle.shear (d x)) = _
        rw [← hH]
        exact hmatch x hx)
  obtain ⟨r, δ, a, b, F, D, L, R, hr, hrsmall, hrs, hδ, _, hδr, hDh, hDzero, hlevels⟩ :=
    M.exists_terminal_flattened_band_level_sets hg P hP hcaps (interior_subset hp)
      hc e he0 hep he hei hform
        (show 0 < min (Real.sqrt s * u / 2) (a₀ / 16) by positivity)
  have hrmatch := hrsmall.trans_le (min_le_left (Real.sqrt s * u / 2) (a₀ / 16))
  have hrchart := hrsmall.trans_le (min_le_right (Real.sqrt s * u / 2) (a₀ / 16))
  obtain ⟨_, ε, _, _, _, hε, _, _, hends⟩ :=
    M.exists_terminal_saddle_cut_resolution hg P hP hcaps (interior_subset hp) hc
      e he0 hep he hei hform zero_lt_one
  let η := min δ (min ε (s / 4)) / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηδ : η < δ := by
    have := min_le_left δ (min ε (s / 4))
    dsimp [η]
    linarith
  have hηε : η ≤ ε := by
    have := (min_le_right δ (min ε (s / 4))).trans (min_le_left ε (s / 4))
    dsimp [η] at hη ⊢
    linarith
  have hηs : η < s / 4 := by
    have := (min_le_right δ (min ε (s / 4))).trans (min_le_right ε (s / 4))
    dsimp [η] at hη ⊢
    linarith
  obtain ⟨ends, hlower, hupper, hcaps3, _⟩ := hends η hη hηε
  have hcard : Fintype.card ends.EndIndex = 3 := by
    rw [← Nat.card_eq_fintype_card, ends.card_endIndex_eq_caps_length, hcaps3]
  let labels : Fin 3 ≃ ends.EndIndex := (Fintype.equivFinOfCardEq hcard).symm
  have hmodel0 : Saddle.shear (d 0) 2 = -1 := by
    rw [hdp]
    exact Saddle.height_saddlePoint
  refine ⟨{
    D := D
    frame := frame
    frame_height := hframe
    frame_isometry := J.isometry
    frame_zero := J.map_zero
    r := r
    delta := δ
    r_pos := hr
    square_source := hrs
    delta_pos := hδ
    delta_lt := hδr
    D_height := hDh
    strips := F
    a := a
    b := b
    leftContact := L
    rightContact := R
    flattened_levels := hlevels
    model := Saddle.shear
    model_kind := Or.inl rfl
    transport := T
    scale := s
    scale_pos := hs
    modelChart := d
    modelChart_zero := hd0
    modelChart_smooth := hd
    modelChart_symm_smooth := hdi
    matchingRadius := u
    matchingRadius_pos := hu
    matching_source := hus
    matching_actual_source := hactual
    transport_height := ?_
    matching := ?_
    ends := ends
    eta := η
    eta_pos := hη
    eta_lt := hηδ
    lowerCut_eq := hlower
    upperCut_eq := hupper
    labels := labels
    modelSeed := modelSeeds
    modelSeed_outside := ?_ }, rfl, hDzero, by dsimp; linarith [hrmatch],
      a₀, ε₀, ha₀, hε₀, by dsimp; linarith [hrchart], haSource, Q, hQ, hQlevel⟩
  · intro y
    rw [hmodel0, sub_neg_eq_add]
    exact hTh y
  · intro x hx
    rw [← hH]
    exact hmatch x hx
  · intro i hi
    rw [hlower, hupper, hTh] at hi
    change inner Real (M.v : E3) (g p) + s * (Saddle.height (modelSeeds i) + 1) ∈
      Icc (inner Real (M.v : E3) (g p) - η)
        (inner Real (M.v : E3) (g p) + η) at hi
    rcases modelSeeds_height i with hlow | hupp
    · rw [hlow] at hi
      linarith [hi.1]
    · rw [hupp] at hi
      linarith [hi.2]



theorem exists_terminal_saddle_geometry_with_planar_chart
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps)
    {p : S2} (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (hunique : ∀ q ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y => inner Real (M.v : E3) (g y)) q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source)
    (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (het : e.target ⊆ interior P.core)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ d : TerminalSaddleGeometry M P p e, d.model = Saddle.shear ∧
      (∀ y, inner Real (M.v : E3) y = inner Real (M.v : E3) (g p) → d.D y = y) ∧
      2 * d.r < Real.sqrt d.scale * d.matchingRadius ∧
      ∃ a ε : Real, 0 < a ∧ 0 < ε ∧ 8 * d.r < a ∧ closedSquare a ⊆ e.source ∧
        ∃ R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          (∀ x ∈ closedSquare a, R x = Saddle.toE2 (d.frame (g (e x)))) ∧
          ∀ x ∈ closedSquare a, ∀ t ∈ Icc (-ε) ε,
            Saddle.toE3 (R x) (inner Real (M.v : E3) (g p) + t) ∈ d.frame '' range g ↔
              -x 0 ^ 2 + x 1 ^ 2 = t := by
  obtain ⟨d, hm, hz, hs, a, ε, ha, hε, hsmall, hsource, R, hR, hlevel⟩ :=
    exists_terminal_saddle_geometry_with_matched_planar_chart
      M hg P hP hcaps hp hc hunique e he0 hep he hei het hform
  exact ⟨d, hm, hz, hs, a, ε, ha, hε, hsmall, hsource, R, hR,
    fun x hx t ht => (hlevel x hx t ht).1⟩



theorem exists_terminal_saddle_geometry_with_matching_square
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps)
    {p : S2} (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (hunique : ∀ q ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y => inner Real (M.v : E3) (g y)) q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source)
    (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (het : e.target ⊆ interior P.core)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ d : TerminalSaddleGeometry M P p e, d.model = Saddle.shear ∧
      (∀ y, inner Real (M.v : E3) y = inner Real (M.v : E3) (g p) → d.D y = y) ∧
      2 * d.r < Real.sqrt d.scale * d.matchingRadius := by
  obtain ⟨d, hmodel, hzero, hsquare, _⟩ := exists_terminal_saddle_geometry_with_planar_chart
    M hg P hP hcaps hp hc hunique e he0 hep he hei het hform
  exact ⟨d, hmodel, hzero, hsquare⟩


theorem exists_terminal_saddle_geometry_with_fixed_critical_level
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps)
    {p : S2} (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (hunique : ∀ q ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y => inner Real (M.v : E3) (g y)) q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source)
    (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (het : e.target ⊆ interior P.core)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ d : TerminalSaddleGeometry M P p e, d.model = Saddle.shear ∧
      ∀ y, inner Real (M.v : E3) y = inner Real (M.v : E3) (g p) → d.D y = y := by
  obtain ⟨d, hmodel, hzero, _⟩ := exists_terminal_saddle_geometry_with_matching_square
    M hg P hP hcaps hp hc hunique e he0 hep he hei het hform
  exact ⟨d, hmodel, hzero⟩



theorem exists_terminal_saddle_geometry
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps)
    {p : S2} (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (_hunique : ∀ q ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y => inner Real (M.v : E3) (g y)) q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source)
    (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (_het : e.target ⊆ interior P.core)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ d : TerminalSaddleGeometry M P p e, d.model = Saddle.shear := by

  obtain ⟨d, hmodel, _⟩ := exists_terminal_saddle_geometry_with_fixed_critical_level
    M hg P hP hcaps hp hc _hunique e he0 hep he hei _het hform
  exact ⟨d, hmodel⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
