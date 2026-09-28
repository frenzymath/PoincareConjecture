import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Geometry
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Matching

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_terminal_nested_saddle_geometry_with_matched_planar_chart
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ d : TerminalSaddleGeometry M P p e,
      d.model = Saddle.Nested.shear (3 / 10) ∧
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
  obtain ⟨p₀, _, s, hs, _, _, d, hd0, hdp, hd, hdi, u, hu, hus, hactual,
      T, H, hH, hTh, _, _, _, hmatch⟩ :=
    Saddle.Nested.exists_filled_nested_saddle_matching (M.tree.embedding_of_mem_leaves hg)
      hv p hc e he0 hep he hei hform zero_lt_one
  obtain ⟨a₀, ε₀, ha₀, hε₀, haSource, Q, hQ, hQlevel⟩ :=
    exists_terminal_raw_matched_morse_coordinates hg frame hframe he0 hep he hei hc hform
      ((Saddle.Nested.shear (3 / 10)).trans T) hs hu hus hactual (by
        intro x hx
        change T (Saddle.Nested.shear (3 / 10) (d x)) = _
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
  let v := u / 4
  have hvpos : 0 < v := by dsimp [v]; positivity
  let q : Fin 3 → E2 := ![WithLp.toLp 2 ![v, 0], WithLp.toLp 2 ![-v, 0],
    WithLp.toLp 2 ![0, v]]
  have hq (i : Fin 3) : q i ∈ closedBall (0 : E2) u := by
    apply closedBall_subset_closedBall (show 2 * v ≤ u by dsimp [v]; linarith)
    apply closedSquare_subset_closedBall hvpos.le
    fin_cases i <;> simp [q, closedSquare, abs_of_pos hvpos, hvpos.le]
  have hseed (i : Fin 3) : inner Real (M.v : E3)
      (T (Saddle.Nested.shear (3 / 10) (d (q i)))) =
      inner Real (M.v : E3) (g p) + s * (-(q i 0)^2 + (q i 1)^2) := by
    rw [← hH, hmatch _ (hq i), hform _ (hactual _ (hq i))]
    simp only [PiLp.smul_apply, smul_eq_mul, mul_pow, Real.sq_sqrt hs.le]
    ring
  let η := min δ (min ε (s * v ^ 2)) / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηδ : η < δ := by
    have := min_le_left δ (min ε (s * v ^ 2))
    dsimp [η] at hη ⊢
    linarith
  have hηε : η ≤ ε := by
    have := (min_le_right δ (min ε (s * v ^ 2))).trans (min_le_left ε (s * v ^ 2))
    dsimp [η] at hη ⊢
    linarith
  have hηs : η < s * v ^ 2 := by
    have := (min_le_right δ (min ε (s * v ^ 2))).trans (min_le_right ε (s * v ^ 2))
    dsimp [η] at hη ⊢
    linarith
  obtain ⟨ends, hlower, hupper, hcaps3, _⟩ := hends η hη hηε
  have hcard : Fintype.card ends.EndIndex = 3 := by
    rw [← Nat.card_eq_fintype_card, ends.card_endIndex_eq_caps_length, hcaps3]
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
    model := Saddle.Nested.shear (3 / 10)
    model_kind := Or.inr rfl
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
    labels := (Fintype.equivFinOfCardEq hcard).symm
    modelSeed := fun i => d (q i)
    modelSeed_outside := ?_ }, rfl, hDzero, by dsimp; linarith [hrmatch],
      a₀, ε₀, ha₀, hε₀, by dsimp; linarith [hrchart], haSource, Q, hQ, hQlevel⟩
  · intro y
    rw [hdp]
    exact hTh y
  · intro x hx
    rw [← hH]
    exact hmatch x hx
  · intro i hi
    rw [hlower, hupper, hseed] at hi
    fin_cases i <;> norm_num [q] at hi <;> nlinarith [hi.1, hi.2]

theorem exists_terminal_nested_saddle_geometry_with_planar_chart
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ d : TerminalSaddleGeometry M P p e,
      d.model = Saddle.Nested.shear (3 / 10) ∧
      (∀ y, inner Real (M.v : E3) y = inner Real (M.v : E3) (g p) → d.D y = y) ∧
      2 * d.r < Real.sqrt d.scale * d.matchingRadius ∧
      ∃ a ε : Real, 0 < a ∧ 0 < ε ∧ 8 * d.r < a ∧ closedSquare a ⊆ e.source ∧
        ∃ R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          (∀ x ∈ closedSquare a, R x = Saddle.toE2 (d.frame (g (e x)))) ∧
          ∀ x ∈ closedSquare a, ∀ t ∈ Icc (-ε) ε,
            Saddle.toE3 (R x) (inner Real (M.v : E3) (g p) + t) ∈ d.frame '' range g ↔
              -x 0 ^ 2 + x 1 ^ 2 = t := by
  obtain ⟨d, hm, hz, hs, a, ε, ha, hε, hsmall, hsource, R, hR, hlevel⟩ :=
    exists_terminal_nested_saddle_geometry_with_matched_planar_chart
      M hg P hP hcaps hp hc e he0 hep he hei hform
  exact ⟨d, hm, hz, hs, a, ε, ha, hε, hsmall, hsource, R, hR,
    fun x hx t ht => (hlevel x hx t ht).1⟩

theorem exists_terminal_nested_saddle_geometry_with_matching_square
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ d : TerminalSaddleGeometry M P p e,
      d.model = Saddle.Nested.shear (3 / 10) ∧
      (∀ y, inner Real (M.v : E3) y = inner Real (M.v : E3) (g p) → d.D y = y) ∧
      2 * d.r < Real.sqrt d.scale * d.matchingRadius := by
  obtain ⟨d, hmodel, hzero, hsquare, _⟩ := exists_terminal_nested_saddle_geometry_with_planar_chart
    M hg P hP hcaps hp hc e he0 hep he hei hform
  exact ⟨d, hmodel, hzero, hsquare⟩

theorem exists_terminal_nested_saddle_geometry
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ d : TerminalSaddleGeometry M P p e,
      d.model = Saddle.Nested.shear (3 / 10) ∧
      ∀ y, inner Real (M.v : E3) y = inner Real (M.v : E3) (g p) → d.D y = y := by
  obtain ⟨d, hmodel, hzero, _⟩ := exists_terminal_nested_saddle_geometry_with_matching_square
    M hg P hP hcaps hp hc e he0 hep he hei hform
  exact ⟨d, hmodel, hzero⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
