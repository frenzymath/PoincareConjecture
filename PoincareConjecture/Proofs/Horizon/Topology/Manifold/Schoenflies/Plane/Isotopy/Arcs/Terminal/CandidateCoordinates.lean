import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelCandidates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ProtectedCoordinates

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

theorem exists_protected_coordinates_of_raw_matched_coordinates
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (hsize : 2 * d.r < Real.sqrt d.scale * d.matchingRadius)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    {a ε : Real} (hε : 0 < ε) (hmargin : 8 * d.r < a)
    (hsource : closedSquare a ⊆ e.source)
    (R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hR : ∀ x ∈ closedSquare a, R x = Saddle.toE2 (d.frame (g (e x))))
    (hraw : ∀ x ∈ closedSquare a, ∀ t ∈ Icc (-ε) ε,
      (Saddle.toE3 (R x) (inner Real (M.v : E3) (g p) + t) ∈ d.frame '' range g ↔
        -x 0 ^ 2 + x 1 ^ 2 = t) ∧
      (Saddle.toE3 (R x) (inner Real (M.v : E3) (g p) + t) ∈
        d.frame '' (d.filledModel '' sphere (0 : E3) 1) ↔ -x 0 ^ 2 + x 1 ^ 2 = t)) :
    ∃ δ : Real, 0 < δ ∧ δ ≤ d.delta ∧ δ < d.eta ∧
      ∃ N : Set E2, IsOpen N ∧ IsCompact (closure N) ∧
        ∃ Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          ContDiff Real ∞ (fun z : Real × E2 => Q z.1 z.2) ∧
          ContDiff Real ∞ (fun z : Real × E2 => (Q z.1).symm z.2) ∧
          (∀ t, ∀ x ∈ closedSquare a, -x 0 ^ 2 + x 1 ^ 2 = t →
            Q t x = Saddle.toE2 (d.flatten (g (e x)))) ∧
          (∀ x ∈ closedSquare a, ∀ t ∈ Icc (-δ) δ,
            (Q t x ∈ d.A (inner Real (M.v : E3) (g p) + t) ↔
              -x 0 ^ 2 + x 1 ^ 2 = t) ∧
            (Q t x ∈ d.B (inner Real (M.v : E3) (g p) + t) ↔
              -x 0 ^ 2 + x 1 ^ 2 = t)) ∧
          (∀ t ∈ Icc (-δ) δ, closure N ⊆ Q t '' openSquare (4 * d.r)) ∧
          (∀ t ∈ Icc (-δ) δ,
            d.A (inner Real (M.v : E3) (g p) + t) ∩ closure N =
              d.B (inner Real (M.v : E3) (g p) + t) ∩ closure N) ∧
          (∀ t ∈ Icc (-δ) δ,
            d.A (inner Real (M.v : E3) (g p) + t) \ closure N =
              d.A (inner Real (M.v : E3) (g p)) \ closure N) ∧
          ∀ t ∈ Icc (-δ) δ, ∀ x ∈ closedSquare d.r,
            -x 0 ^ 2 + x 1 ^ 2 = t → Saddle.toE2 (d.flatten (g (e x))) ∈ N := by
  let c := inner Real (M.v : E3) (g p)
  let Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
    fun t => R.trans (terminalHeightFiber d (c + t))
  have hQ : ContDiff Real ∞ (fun z : Real × E2 => Q z.1 z.2) :=
    (terminalHeightFiber_contDiff d).comp
      (f := fun z : Real × E2 => (c + z.1, R z.2))
      ((contDiff_const.add contDiff_fst).prodMk (R.contDiff.comp contDiff_snd))
  have hQi : ContDiff Real ∞ (fun z : Real × E2 => (Q z.1).symm z.2) := by
    change ContDiff Real ∞ (fun z : Real × E2 =>
      R.symm ((terminalHeightFiber d (c + z.1)).symm z.2))
    exact R.symm.contDiff.comp ((terminalHeightFiber_symm_contDiff d).comp
      (f := fun z : Real × E2 => (c + z.1, z.2))
      ((contDiff_const.add contDiff_fst).prodMk contDiff_snd))
  have hpatch (t : Real) (x : E2) (hx : x ∈ closedSquare a)
      (hxt : -x 0 ^ 2 + x 1 ^ 2 = t) :
      Q t x = Saddle.toE2 (d.flatten (g (e x))) := by
    change terminalHeightFiber d (c + t) (R x) = _
    rw [terminalHeightFiber_apply]
    have hh : Saddle.toE3 (R x) (c + t) = d.frame (g (e x)) := by
      have hp := hR x hx
      have hz := d.frame_height (g (e x))
      rw [hform x (hsource hx)] at hz
      ext i
      fin_cases i
      · exact congrArg (fun y : E2 => y 0) hp
      · exact congrArg (fun y : E2 => y 1) hp
      · change c + t = d.frame (g (e x)) 2
        dsimp [c]
        linarith
    rw [hh, d.frame.symm_apply_apply]
    rfl
  have hslice (x : E2) (hx : x ∈ closedSquare a) (t : Real) (ht : t ∈ Icc (-ε) ε) :
      (Q t x ∈ d.A (c + t) ↔ -x 0 ^ 2 + x 1 ^ 2 = t) ∧
      (Q t x ∈ d.B (c + t) ↔ -x 0 ^ 2 + x 1 ^ 2 = t) :=
    ⟨(terminalHeightFiber_mem_actual_slice_iff d (c + t) (R x)).trans (hraw x hx t ht).1,
      (terminalHeightFiber_mem_model_slice_iff d (c + t) (R x)).trans (hraw x hx t ht).2⟩
  have hra : d.r < a := by linarith [d.r_pos]
  have hrsource : closedSquare d.r ⊆ closedSquare a :=
    fun x hx => ⟨hx.1.trans hra.le, hx.2.trans hra.le⟩
  let V := Q 0 '' openSquare (2 * d.r)
  have hV : IsOpen V := (Q 0).toHomeomorph.isOpenMap _ (isOpen_openSquare _)
  have hcritical (x : E2) (hx : x ∈ closedSquare d.r)
      (hz : (d.flatten (g (e x))) 2 = inner Real (M.v : E3) (g p)) :
      Saddle.toE2 (d.flatten (g (e x))) ∈ V := by
    have hxt : -x 0 ^ 2 + x 1 ^ 2 = 0 := by
      change d.frame (d.D (g (e x))) 2 = _ at hz
      rw [d.frame_height, d.D_height, hform x (d.square_source hx)] at hz
      linarith
    refine ⟨x, ?_, hpatch 0 x (hrsource hx) hxt⟩
    exact ⟨hx.1.trans_lt (by linarith [d.r_pos]), hx.2.trans_lt (by linarith [d.r_pos])⟩
  obtain ⟨εN, hεN, hεNd, N, hN, hNc, hNV, hcommon, hstationary, hprotected⟩ :=
    exists_terminal_stationary_exterior_neighborhood_within hg d hsize hform V hV hcritical
  have hNinside : closure N ⊆ Q 0 '' openSquare (4 * d.r) := by
    apply hNV.trans
    apply image_mono
    intro x hx
    exact ⟨hx.1.trans (by linarith [d.r_pos]), hx.2.trans (by linarith [d.r_pos])⟩
  obtain ⟨εQ, hεQ, hinside⟩ := exists_uniform_compact_subset_moving_image Q hQi.continuous
    hNc (isOpen_openSquare _) hNinside
  let δ := min ε (min εN (min εQ (d.eta / 2)))
  have hδ : 0 < δ := lt_min hε (lt_min hεN (lt_min hεQ (half_pos d.eta_pos)))
  have hδε : δ ≤ ε := min_le_left _ _
  have hδN : δ ≤ εN := (min_le_right _ _).trans (min_le_left _ _)
  have hδQ : δ ≤ εQ :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδη : δ < d.eta :=
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans_lt
      (half_lt_self d.eta_pos)
  have htime {t : Real} (ht : t ∈ Icc (-δ) δ) : t ∈ Icc (-εN) εN :=
    ⟨by linarith [ht.1], ht.2.trans hδN⟩
  refine ⟨δ, hδ, hδN.trans hεNd, hδη, N, hN, hNc, Q, hQ, hQi, hpatch,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx t ht
    exact hslice x hx t ⟨by linarith [ht.1], ht.2.trans hδε⟩
  · intro t ht
    exact hinside t ((abs_le.mpr ht).trans hδQ)
  · intro t ht
    exact hcommon t (htime ht)
  · intro t ht
    exact hstationary t (htime ht)
  · intro t ht
    exact hprotected t (htime ht)

theorem exists_terminal_model_candidates_with_protected_coordinates_and_actual_strips
    (M : SphereMorseReduction f) (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g)
    (hP : P.Protects ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
      {q | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}))
    (hcaps : P.PreservesCaps) (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ ds : Fin 3 → TerminalSaddleGeometry M P p e,
      (ds 0).model = Saddle.shear ∧
      (ds 1).model = Saddle.Nested.shear (3 / 10) ∧
      (ds 2).model = Saddle.Nested.shear (3 / 10) ∧
      (ds 0).modelChart 0 = Saddle.saddlePoint ∧
      (ds 2).modelChart = negativeBranchReflectedChart (ds 1).modelChart ∧
      1 < Saddle.Nested.height ((ds 1).modelChart 0) ∧
      mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.Nested.height ((ds 1).modelChart 0) = 0 ∧
      (∀ i, (ds i).D = (ds 0).D ∧ (ds i).frame = (ds 0).frame ∧
        (ds i).r = (ds 0).r ∧ (ds i).delta = (ds 0).delta ∧
        (ds i).strips = (ds 0).strips ∧ (ds i).a = (ds 0).a ∧
        (ds i).b = (ds 0).b ∧ (ds i).leftContact = (ds 0).leftContact ∧
        (ds i).rightContact = (ds 0).rightContact ∧ (ds i).ends = (ds 0).ends ∧
        (ds i).eta = (ds 0).eta ∧ (ds i).scale = (ds 0).scale) ∧
      (Nat.card (ds 0).ends.LowerCutIndex = 1 ∨
        Nat.card (ds 0).ends.LowerCutIndex = 2) ∧
      (∀ i, Nonempty (ActualStripData (ds i))) ∧
      ∀ i,
        (∀ y, inner Real (M.v : E3) y = inner Real (M.v : E3) (g p) →
          (ds i).D y = y) ∧
        2 * (ds i).r < Real.sqrt (ds i).scale * (ds i).matchingRadius ∧
        ∃ a δ : Real, 0 < a ∧ 0 < δ ∧ 8 * (ds i).r < a ∧
          δ ≤ (ds i).delta ∧ δ < (ds i).eta ∧ closedSquare a ⊆ e.source ∧
          ∃ N : Set E2, IsOpen N ∧ IsCompact (closure N) ∧
            ∃ Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
              ContDiff Real ∞ (fun z : Real × E2 => Q z.1 z.2) ∧
              ContDiff Real ∞ (fun z : Real × E2 => (Q z.1).symm z.2) ∧
              (∀ t, ∀ x ∈ closedSquare a, -x 0 ^ 2 + x 1 ^ 2 = t →
                Q t x = Saddle.toE2 ((ds i).flatten (g (e x)))) ∧
              (∀ x ∈ closedSquare a, ∀ t ∈ Icc (-δ) δ,
                (Q t x ∈ (ds i).A (inner Real (M.v : E3) (g p) + t) ↔
                  -x 0 ^ 2 + x 1 ^ 2 = t) ∧
                (Q t x ∈ (ds i).B (inner Real (M.v : E3) (g p) + t) ↔
                  -x 0 ^ 2 + x 1 ^ 2 = t)) ∧
              (∀ t ∈ Icc (-δ) δ, closure N ⊆ Q t '' openSquare (4 * (ds i).r)) ∧
              (∀ t ∈ Icc (-δ) δ,
                (ds i).A (inner Real (M.v : E3) (g p) + t) ∩ closure N =
                  (ds i).B (inner Real (M.v : E3) (g p) + t) ∩ closure N) ∧
              (∀ t ∈ Icc (-δ) δ,
                (ds i).A (inner Real (M.v : E3) (g p) + t) \ closure N =
                  (ds i).A (inner Real (M.v : E3) (g p)) \ closure N) ∧
              ∀ t ∈ Icc (-δ) δ, ∀ x ∈ closedSquare (ds i).r,
                -x 0 ^ 2 + x 1 ^ 2 = t →
                  Saddle.toE2 ((ds i).flatten (g (e x))) ∈ N := by
  obtain ⟨ds, hm₀, hm₁, hm₂, hc₀, hreflect, hc₁height, hc₁crit,
      hshared, hcount, hstrips, hraw⟩ :=
    exists_terminal_model_candidates_with_actual_strips M hg P hP hcaps hp hc e he0 hep he hei hform
  refine ⟨ds, hm₀, hm₁, hm₂, hc₀, hreflect, hc₁height, hc₁crit, hshared, hcount, hstrips, ?_⟩
  intro i
  obtain ⟨hfixed, hsize, a, ε, ha, hε, hmargin, hsource, R, hR, hslice⟩ := hraw i
  obtain ⟨δ, hδ, hδd, hδη, N, hN, hNc, Q, hQ, hQi, hpatch,
      hlevel, hinside, hcommon, hstationary, hprotected⟩ :=
    exists_protected_coordinates_of_raw_matched_coordinates hg (ds i) hsize hform
      hε hmargin hsource R hR hslice
  exact ⟨hfixed, hsize, a, δ, ha, hδ, hmargin, hδd, hδη, hsource,
    N, hN, hNc, Q, hQ, hQi, hpatch, hlevel, hinside, hcommon, hstationary, hprotected⟩

theorem exists_terminal_model_candidates_with_protected_coordinates
    (M : SphereMorseReduction f) (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g)
    (hP : P.Protects ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
      {q | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}))
    (hcaps : P.PreservesCaps) (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ ds : Fin 3 → TerminalSaddleGeometry M P p e,
      (ds 0).model = Saddle.shear ∧
      (ds 1).model = Saddle.Nested.shear (3 / 10) ∧
      (ds 2).model = Saddle.Nested.shear (3 / 10) ∧
      (ds 0).modelChart 0 = Saddle.saddlePoint ∧
      (ds 2).modelChart = negativeBranchReflectedChart (ds 1).modelChart ∧
      1 < Saddle.Nested.height ((ds 1).modelChart 0) ∧
      mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.Nested.height ((ds 1).modelChart 0) = 0 ∧
      (∀ i, (ds i).D = (ds 0).D ∧ (ds i).frame = (ds 0).frame ∧
        (ds i).r = (ds 0).r ∧ (ds i).delta = (ds 0).delta ∧
        (ds i).strips = (ds 0).strips ∧ (ds i).a = (ds 0).a ∧
        (ds i).b = (ds 0).b ∧ (ds i).leftContact = (ds 0).leftContact ∧
        (ds i).rightContact = (ds 0).rightContact ∧ (ds i).ends = (ds 0).ends ∧
        (ds i).eta = (ds 0).eta ∧ (ds i).scale = (ds 0).scale) ∧
      (Nat.card (ds 0).ends.LowerCutIndex = 1 ∨
        Nat.card (ds 0).ends.LowerCutIndex = 2) ∧
      ∀ i,
        (∀ y, inner Real (M.v : E3) y = inner Real (M.v : E3) (g p) →
          (ds i).D y = y) ∧
        2 * (ds i).r < Real.sqrt (ds i).scale * (ds i).matchingRadius ∧
        ∃ a δ : Real, 0 < a ∧ 0 < δ ∧ 8 * (ds i).r < a ∧
          δ ≤ (ds i).delta ∧ δ < (ds i).eta ∧ closedSquare a ⊆ e.source ∧
          ∃ N : Set E2, IsOpen N ∧ IsCompact (closure N) ∧
            ∃ Q : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
              ContDiff Real ∞ (fun z : Real × E2 => Q z.1 z.2) ∧
              ContDiff Real ∞ (fun z : Real × E2 => (Q z.1).symm z.2) ∧
              (∀ t, ∀ x ∈ closedSquare a, -x 0 ^ 2 + x 1 ^ 2 = t →
                Q t x = Saddle.toE2 ((ds i).flatten (g (e x)))) ∧
              (∀ x ∈ closedSquare a, ∀ t ∈ Icc (-δ) δ,
                (Q t x ∈ (ds i).A (inner Real (M.v : E3) (g p) + t) ↔
                  -x 0 ^ 2 + x 1 ^ 2 = t) ∧
                (Q t x ∈ (ds i).B (inner Real (M.v : E3) (g p) + t) ↔
                  -x 0 ^ 2 + x 1 ^ 2 = t)) ∧
              (∀ t ∈ Icc (-δ) δ, closure N ⊆ Q t '' openSquare (4 * (ds i).r)) ∧
              (∀ t ∈ Icc (-δ) δ,
                (ds i).A (inner Real (M.v : E3) (g p) + t) ∩ closure N =
                  (ds i).B (inner Real (M.v : E3) (g p) + t) ∩ closure N) ∧
              (∀ t ∈ Icc (-δ) δ,
                (ds i).A (inner Real (M.v : E3) (g p) + t) \ closure N =
                  (ds i).A (inner Real (M.v : E3) (g p)) \ closure N) ∧
              ∀ t ∈ Icc (-δ) δ, ∀ x ∈ closedSquare (ds i).r,
                -x 0 ^ 2 + x 1 ^ 2 = t →
                  Saddle.toE2 ((ds i).flatten (g (e x))) ∈ N := by
  obtain ⟨ds, hm₀, hm₁, hm₂, hc₀, hreflect, hc₁height, hc₁crit,
      hshared, hcount, _, hcoordinates⟩ :=
    exists_terminal_model_candidates_with_protected_coordinates_and_actual_strips
      M hg P hP hcaps hp hc e he0 hep he hei hform
  exact ⟨ds, hm₀, hm₁, hm₂, hc₀, hreflect, hc₁height, hc₁crit,
    hshared, hcount, hcoordinates⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
