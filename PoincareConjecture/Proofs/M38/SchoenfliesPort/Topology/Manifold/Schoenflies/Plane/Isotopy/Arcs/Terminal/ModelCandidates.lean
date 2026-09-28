import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Geometry
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.NestedCandidatePair
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ActualStripData
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.FlattenedStrips







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open _root_.PoincareConjecture

namespace M38Schoenflies



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

private def minThree (v : Fin 3 → Real) := min (v 0) (min (v 1) (v 2))

private theorem minThree_pos {v : Fin 3 → Real} (h : ∀ i, 0 < v i) :
    0 < minThree v := lt_min (h 0) (lt_min (h 1) (h 2))

private theorem minThree_le (v : Fin 3 → Real) (i : Fin 3) : minThree v ≤ v i := by
  fin_cases i
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)




theorem exists_terminal_model_candidates_with_actual_strips
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
        ∃ a ε : Real, 0 < a ∧ 0 < ε ∧ 8 * (ds i).r < a ∧
          closedSquare a ⊆ e.source ∧
          ∃ R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
            (∀ x ∈ closedSquare a, R x = Saddle.toE2 ((ds i).frame (g (e x)))) ∧
            ∀ x ∈ closedSquare a, ∀ t ∈ Icc (-ε) ε,
              (Saddle.toE3 (R x) (inner Real (M.v : E3) (g p) + t) ∈
                (ds i).frame '' range g ↔ -x 0 ^ 2 + x 1 ^ 2 = t) ∧
              (Saddle.toE3 (R x) (inner Real (M.v : E3) (g p) + t) ∈
                (ds i).frame '' ((ds i).filledModel '' sphere (0 : E3) 1) ↔
                -x 0 ^ 2 + x 1 ^ 2 = t) := by
  have hv : ‖(M.v : E3)‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using M.v.property
  obtain ⟨s, hs, _, _, d₀, hd₀0, hd₀p, hd₀, hdi₀, u₀, hu₀, hus₀, hactual₀,
      T₀, H₀, hH₀, hTh₀, _, _, _, _, hmatch₀⟩ :=
    Saddle.exists_filled_saddle_matching (M.tree.embedding_of_mem_leaves hg) hv p hc
      e he0 hep he hei hform zero_lt_one
  obtain ⟨d₁, hd₁0, hd₁height, hd₁crit, hd₁, hdi₁, _, u₁, hu₁, hus₁,
      hus₂, hactual₁, T₁, H₁, hH₁, hTh₁, _, _, _, hmatch₁, hmatch₂, _⟩ :=
    exists_filled_nested_candidate_pair (M.tree.embedding_of_mem_leaves hg) hv p hc
      e he0 hep he hei hform hs
  let model : Fin 3 → Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
    ![Saddle.shear, Saddle.Nested.shear (3 / 10), Saddle.Nested.shear (3 / 10)]
  let chart : Fin 3 → OpenPartialHomeomorph E2 S2 :=
    ![d₀, d₁, negativeBranchReflectedChart d₁]
  let transport : Fin 3 → Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ := ![T₀, T₁ 0, T₁ 1]
  let u : Fin 3 → Real := ![u₀, u₁, u₁]
  have hu (i) : 0 < u i := by fin_cases i <;> assumption
  have hkind (i) : model i = Saddle.shear ∨
      model i = Saddle.Nested.shear (3 / 10) := by
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
  have hzero (i) : 0 ∈ (chart i).source := by
    fin_cases i
    · exact hd₀0
    · exact hd₁0
    · apply (mem_negativeBranchReflectedChart_source d₁ 0).mpr
      simpa only [map_zero] using hd₁0
  have hchart (i) : ContMDiffOn (𝓡 2) (𝓡 2) ∞ (chart i) (chart i).source := by
    fin_cases i
    · exact hd₀
    · exact hd₁
    · exact negativeBranchReflectedChart_smooth d₁ hd₁
  have hcharti (i) : ContMDiffOn (𝓡 2) (𝓡 2) ∞ (chart i).symm (chart i).target := by
    fin_cases i
    · exact hdi₀
    · exact hdi₁
    · exact negativeBranchReflectedChart_symm_smooth d₁ hdi₁
  have hsource (i) : closedBall (0 : E2) (u i) ⊆ (chart i).source := by
    fin_cases i <;> assumption
  have hactual (i) : ∀ x ∈ closedBall (0 : E2) (u i), Real.sqrt s • x ∈ e.source := by
    fin_cases i <;> assumption
  have hheight (i) (y : E3) : inner Real (M.v : E3) (transport i y) =
      inner Real (M.v : E3) (g p) + s * (y 2 - model i (chart i 0) 2) := by
    fin_cases i
    · change inner Real (M.v : E3) (T₀ y) = _
      rw [hTh₀]
      change _ = _ + s * (y 2 - Saddle.height (d₀ 0))
      rw [hd₀p, Saddle.height_saddlePoint]
      ring
    · exact hTh₁ 0 y
    · change inner Real (M.v : E3) (T₁ 1 y) =
        inner Real (M.v : E3) (g p) + s *
          (y 2 - Saddle.Nested.height (negativeBranchReflectedChart d₁ 0))
      simpa only [negativeBranchReflectedChart_zero] using hTh₁ 1 y
  have hmatch (i) : ∀ x ∈ closedBall (0 : E2) (u i),
      transport i (model i (chart i x)) = g (e (Real.sqrt s • x)) := by
    fin_cases i
    · intro x hx
      change T₀ (Saddle.shear (d₀ x)) = _
      rw [← hH₀]
      exact hmatch₀ x hx
    · intro x hx
      change T₁ 0 (Saddle.Nested.shear (3 / 10) (d₁ x)) = _
      rw [← hH₁]
      exact hmatch₁ x hx
    · intro x hx
      change T₁ 1 (Saddle.Nested.shear (3 / 10) (negativeBranchReflectedChart d₁ x)) = _
      rw [← hH₁]
      exact hmatch₂ x hx
  let axis : E3 := EuclideanSpace.single 2 1
  let J : E3 ≃ₗᵢ[Real] E3 := Submodule.reflection (Real ∙ ((M.v : E3) - axis))ᗮ
  have hJv : J M.v = axis := Submodule.reflection_sub (by simp [axis, hv])
  let frame := J.toContinuousLinearEquiv.toDiffeomorph
  have hframe (y : E3) : frame y 2 = inner Real (M.v : E3) y := by
    have hinner := J.inner_map_map (M.v : E3) y
    rw [hJv] at hinner
    simpa [frame, axis, PiLp.inner_apply] using hinner
  have hcoords (i : Fin 3) :=
    exists_terminal_raw_matched_morse_coordinates hg frame hframe he0 hep he hei hc hform
      ((model i).trans (transport i)) hs (hu i) (hsource i) (hactual i) (hmatch i)
  choose A ε hA hε hAS Q hQ hQlevel using hcoords
  let bound : Fin 3 → Real := fun i => min (Real.sqrt s * u i / 2) (A i / 16)
  have hbound (i) : 0 < bound i := by
    dsimp [bound]
    exact lt_min (div_pos (mul_pos (Real.sqrt_pos.mpr hs) (hu i)) (by norm_num))
      (div_pos (hA i) (by norm_num))
  obtain ⟨r, w, ηstrip, δ, a, b, a₀, b₀, F, K, V, D, labels, L, R,
      hr, hrsmall, hrs, hw, hηstrip, hηw, hηbound, hab, hFs, hF, hFi, hFheight,
      hFdisjoint, hcore, hband, hchain, hcentral, hendpoints, hpair,
      hK, hKband, hV, hpV, hDV, hDK, hDh, hDzero, hflat,
      hδ, hδηstrip, _, hδr, hlabels, hcontacts, hrecut⟩ :=
    exists_terminal_flattened_strips M hg P hP hcaps (interior_subset hp)
      hc e he0 hep he hei hform (minThree_pos hbound)
  have hrmatch (i) : 2 * r < Real.sqrt s * u i := by
    have hh := hrsmall.trans_le ((minThree_le bound i).trans (min_le_left _ _))
    linarith
  have hrchart (i) : 8 * r < A i := by
    have hh := hrsmall.trans_le ((minThree_le bound i).trans (min_le_right _ _))
    linarith
  obtain ⟨_, εend, _, _, _, hεend, _, _, hends⟩ :=
    M.exists_terminal_saddle_cut_resolution hg P hP hcaps (interior_subset hp) hc
      e he0 hep he hei hform zero_lt_one
  let v : Fin 3 → Real := fun i => u i / 4
  have hvpos (i) : 0 < v i := by dsimp [v]; exact div_pos (hu i) (by norm_num)
  let q : Fin 3 → Fin 3 → E2 := fun i =>
    ![WithLp.toLp 2 ![v i, 0], WithLp.toLp 2 ![-v i, 0], WithLp.toLp 2 ![0, v i]]
  have hq (i j) : q i j ∈ closedBall (0 : E2) (u i) := by
    apply closedBall_subset_closedBall (show 2 * v i ≤ u i by dsimp [v]; linarith [hu i])
    apply closedSquare_subset_closedBall (hvpos i).le
    fin_cases j <;> simp [q, closedSquare, abs_of_pos (hvpos i), (hvpos i).le]
  have hseed (i j) : inner Real (M.v : E3) (transport i (model i (chart i (q i j)))) =
      inner Real (M.v : E3) (g p) + s * (-(q i j 0)^2 + (q i j 1)^2) := by
    rw [hmatch i _ (hq i j), hform _ (hactual i _ (hq i j))]
    simp only [PiLp.smul_apply, smul_eq_mul, mul_pow, Real.sq_sqrt hs.le]
    ring
  let gap : Fin 3 → Real := fun i => s * v i ^ 2
  have hgap (i) : 0 < gap i := mul_pos hs (sq_pos_of_pos (hvpos i))
  let η := min δ (min εend (minThree gap)) / 2
  have hη : 0 < η := by
    exact div_pos (lt_min hδ (lt_min hεend (minThree_pos hgap))) (by norm_num)
  have hηδ : η < δ := by
    have := min_le_left δ (min εend (minThree gap))
    dsimp [η] at hη ⊢
    linarith
  have hηε : η ≤ εend := by
    have := (min_le_right δ (min εend (minThree gap))).trans (min_le_left _ _)
    dsimp [η] at hη ⊢
    linarith
  have hηgap (i) : η < gap i := by
    have := ((min_le_right δ (min εend (minThree gap))).trans
      (min_le_right _ _)).trans (minThree_le gap i)
    dsimp [η] at hη ⊢
    linarith
  obtain ⟨ends, hlower, hupper, hcaps3, halternative⟩ := hends η hη hηε
  have hcount : Nat.card ends.LowerCutIndex = 1 ∨ Nat.card ends.LowerCutIndex = 2 := by
    rcases halternative with ⟨hone, _⟩ | ⟨_, E, _⟩
    · exact Or.inl hone
    · exact Or.inr (by simpa using (Nat.card_congr E).symm)
  have hcard : Fintype.card ends.EndIndex = 3 := by
    rw [← Nat.card_eq_fintype_card, ends.card_endIndex_eq_caps_length, hcaps3]
  let ds : Fin 3 → TerminalSaddleGeometry M P p e := fun i => {
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
    flattened_levels := by
      intro t ht
      obtain ⟨hAB, _, hlevel, hexterior⟩ := hrecut t ht
      exact ⟨fun j => ⟨(hAB j).1, (hAB j).2.1, (hAB j).2.2.1,
        (hAB j).2.2.2.1, (hAB j).2.2.2.2.1⟩, hlevel, hexterior⟩
    model := model i
    model_kind := hkind i
    transport := transport i
    scale := s
    scale_pos := hs
    modelChart := chart i
    modelChart_zero := hzero i
    modelChart_smooth := hchart i
    modelChart_symm_smooth := hcharti i
    matchingRadius := u i
    matchingRadius_pos := hu i
    matching_source := hsource i
    matching_actual_source := hactual i
    transport_height := hheight i
    matching := hmatch i
    ends := ends
    eta := η
    eta_pos := hη
    eta_lt := hηδ
    lowerCut_eq := hlower
    upperCut_eq := hupper
    labels := (Fintype.equivFinOfCardEq hcard).symm
    modelSeed := fun j => chart i (q i j)
    modelSeed_outside := by
      intro j hj
      rw [hlower, hupper, hseed] at hj
      have hgap' := hηgap i
      dsimp [gap] at hgap'
      fin_cases j <;> norm_num [q] at hj <;> nlinarith [hj.1, hj.2] }
  have hstripData (i : Fin 3) : Nonempty (ActualStripData (ds i)) := ⟨{
    width := w
    bandHeight := ηstrip
    ambientBound := minThree bound
    centralLeft := a₀
    centralRight := b₀
    contactLabels := labels
    support := K
    fixedNeighborhood := V
    width_pos := hw
    bandHeight_pos := hηstrip
    bandHeight_lt_width := hηw
    bandHeight_lt_bound := hηbound
    radius_lt_bound := hrsmall
    delta_lt_bandHeight := hδηstrip
    interval_nonempty := hab
    source_eq := hFs
    smooth := hF
    symm_smooth := hFi
    height := hFheight
    disjoint := hFdisjoint
    band_in_core := hcore
    band_cover := hband
    central_chain := hchain
    central_cover := hcentral
    central_endpoints := hendpoints
    contact_pairing := hpair
    support_compact := hK
    support_height := hKband
    fixedNeighborhood_open := hV
    center_mem_fixedNeighborhood := hpV
    fixed_on_neighborhood := hDV
    fixed_off_support := hDK
    fixed_critical_plane := hDzero
    flattening := hflat
    endpoint_labels := hlabels
    contacts_zero := hcontacts
    recut_geometry := fun t ht => ⟨(hrecut t ht).1, (hrecut t ht).2.1⟩ }⟩
  refine ⟨ds, rfl, rfl, rfl, hd₀p, rfl, hd₁height, hd₁crit, ?_, ?_⟩
  · intro i
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨hcount, hstripData, ?_⟩
    intro i
    exact ⟨hDzero, hrmatch i, A i, ε i, hA i, hε i, hrchart i, hAS i,
      Q i, hQ i, hQlevel i⟩



theorem exists_terminal_model_candidates
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
        ∃ a ε : Real, 0 < a ∧ 0 < ε ∧ 8 * (ds i).r < a ∧
          closedSquare a ⊆ e.source ∧
          ∃ R : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
            (∀ x ∈ closedSquare a, R x = Saddle.toE2 ((ds i).frame (g (e x)))) ∧
            ∀ x ∈ closedSquare a, ∀ t ∈ Icc (-ε) ε,
              (Saddle.toE3 (R x) (inner Real (M.v : E3) (g p) + t) ∈
                (ds i).frame '' range g ↔ -x 0 ^ 2 + x 1 ^ 2 = t) ∧
              (Saddle.toE3 (R x) (inner Real (M.v : E3) (g p) + t) ∈
                (ds i).frame '' ((ds i).filledModel '' sphere (0 : E3) 1) ↔
                -x 0 ^ 2 + x 1 ^ 2 = t) := by
  obtain ⟨ds, hm₀, hm₁, hm₂, hc₀, hreflect, hc₁height, hc₁crit,
      hshared, hcount, _, hraw⟩ :=
    exists_terminal_model_candidates_with_actual_strips M hg P hP hcaps hp hc e he0 hep he hei hform
  exact ⟨ds, hm₀, hm₁, hm₂, hc₀, hreflect, hc₁height, hc₁crit, hshared, hcount, hraw⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies
