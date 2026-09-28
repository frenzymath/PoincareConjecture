import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.CandidateCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.CandidateCircles
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.CoordinateTransport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ProtectedCircleAnchor
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.TransportAnchor
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.SpatialProtection



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



theorem exists_terminal_planar_slab_or_one_lower_end
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g)
    (hP : P.Protects ((fun q => inner Real (M.v : E3) (M.D (f q))) ''
      {q | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real (M.v : E3) (M.D (f y))) q = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ interior P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (hunique : ∀ q ∈ P.core, mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y => inner Real (M.v : E3) (g y)) q = 0 → q = p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ d : TerminalSaddleGeometry M P p e,
      Nat.card d.ends.LowerCutIndex = 1 ∨
      ∃ δ : Real, 0 < δ ∧ δ ≤ d.delta ∧ δ < d.eta ∧
        ∃ (K : Set E2) (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞),
          IsCompact K ∧ (∀ z x, Φ 0 z x = x) ∧
          ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2) ∧
          ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2) ∧
          (∀ u z x, x ∉ K → Φ u z x = x) ∧
          (∀ z ∈ Icc (inner Real (M.v : E3) (g p) - δ)
              (inner Real (M.v : E3) (g p) + δ), Φ 1 z '' d.A z = d.B z) ∧
          ∃ ρ : Real, 0 < ρ ∧ ∃ U : Set E3, IsOpen U ∧
            closedSquare ρ ⊆ e.source ∧
            (∀ x ∈ closedSquare ρ,
              (Real.sqrt d.scale)⁻¹ • x ∈ closedBall (0 : E2) d.matchingRadius) ∧
            (d.flatten ∘ g ∘ e) '' closedSquare ρ ⊆ U ∧
            ∀ u, EqOn (planarHeightMap Φ u) id U := by
  classical
  obtain ⟨ds, hm0, hm1, hm2, _, hchart, _, _, hshared, hcount, hstrips, hcoords⟩ :=
    exists_terminal_model_candidates_with_protected_coordinates_and_actual_strips
      M hg P hP hcaps hp hc e he0 hep he hei hform
  rcases hcount with hone | htwo
  · exact ⟨ds 0, Or.inl hone⟩
  have hsize (i) := (hcoords i).2.1
  have hcs (i : Fin 3) := (hcoords i).2.2
  choose a ε ha hε hmargin hεd hεη hsource N0 hN0 hN0c Q hQ hQi hpatch hlevel
    hinside0 hcommon0 hstationary0 hprotected0 using hcs
  have htrans (i : Fin 3) := exists_terminal_coordinate_model_transport (ds i)
    (Classical.choice (hstrips i)) (M.tree.embedding_of_mem_leaves hg)
    (hsize i) hform (Q i) (hQi i) (hε i) (hmargin i) (hpatch i)
  choose δ C K O N V hδ hδε hδd hδη hC hCreg hK hO hCO hKO hN hCN hNreg
    hV hpatchV hpatchC hfiber hstationary hcommon hinside Ψ hΨ0 hΨ hΨi hΨfix hΨO hmove
    using htrans
  have hscale : (ds 2).scale = (ds 1).scale :=
    (hshared 2).2.2.2.2.2.2.2.2.2.2.2.trans (hshared 1).2.2.2.2.2.2.2.2.2.2.2.symm
  obtain ⟨εC, hεC, hcircles⟩ := exists_matching_terminal_candidate_circles hg ds
    hm0 hm1 hm2 hscale hchart (fun i => (hshared i).1) (fun i => (hshared i).2.1)
    hP hcaps (interior_subset hp) hc hunique he0 hep he hei hform htwo
  let β := min (δ 0) (min (δ 1) (δ 2))
  have hβ : 0 < β := lt_min (hδ 0) (lt_min (hδ 1) (hδ 2))
  have hβδ (i : Fin 3) : β ≤ δ i := by
    fin_cases i
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  let τ := min εC (min β ((ds 0).r ^ 2)) / 2
  have hτ : 0 < τ := half_pos (lt_min hεC (lt_min hβ (sq_pos_of_pos (ds 0).r_pos)))
  have hτεC : τ < εC := (half_lt_self
    (lt_min hεC (lt_min hβ (sq_pos_of_pos (ds 0).r_pos)))).trans_le (min_le_left _ _)
  have hτβ : τ < β := by
    have := min_le_right εC (min β ((ds 0).r ^ 2))
    have := min_le_left β ((ds 0).r ^ 2)
    dsimp [τ] at hτ ⊢
    linarith
  have hτr : τ < (ds 0).r ^ 2 := by
    have := min_le_right εC (min β ((ds 0).r ^ 2))
    have := min_le_right β ((ds 0).r ^ 2)
    dsimp [τ] at hτ ⊢
    linarith
  obtain ⟨k, AC, BC, hAC, hBC, hiAC, hiBC, hcoverAC, hcoverBC, hmarkAC, hmarkBC, hnest⟩ :=
    hcircles τ ⟨hτ, hτεC.le⟩
  have hτδ : τ ≤ δ k := (hτβ.trans_le (hβδ k)).le
  have hτrk : τ < (ds k).r ^ 2 := by rwa [(hshared k).2.2.1]
  have htime : -τ ∈ Icc (-(δ k)) (δ k) := ⟨by linarith, by linarith [hδ k]⟩
  have htimeε : -τ ∈ Icc (-(ε k)) (ε k) :=
    ⟨by linarith [hδε k], by linarith [hε k]⟩
  have hcenter (i : Fin 2) : Q k (-τ) (negativeLevelArc τ i 0) ∈
      range (AC i) ∩ range (BC i) := by
    have hta : τ < (a k) ^ 2 := by nlinarith [hmargin k, (ds k).r_pos]
    have hx : negativeLevelArc τ i 0 ∈ closedSquare (a k) :=
      (negativeLevelArc_mem_closedSquare (ha k) hτ hta i 0).mpr
        ⟨by linarith [hyperbolaRadius_pos hta], (hyperbolaRadius_pos hta).le⟩
    rw [hpatch k (-τ) _ hx (negativeLevelArc_height hτ i 0)]
    exact ⟨hmarkAC i, hmarkBC i⟩
  have hclosed : closure (C k) = C k := (hC k).isClosed.closure_eq
  obtain ⟨KQ, hKQ, hKQC, R, hR0, hR, hRi, hRfix, _, hmatch, UQ, hUQ, hCUQ, hRUQ⟩ :=
    exists_terminal_protected_negative_circle_anchor (ds k) (Q k (-τ)) (hmargin k)
      hτ hτrk (by
        intro x hx
        simpa only [sub_eq_add_neg] using hlevel k x hx (-τ) htimeε)
      AC BC hAC hBC hiAC hiBC hcoverAC hcoverBC hnest hcenter (C k)
      (by rw [hclosed]; exact hinside k (-τ) htime)
  rw [hclosed] at hCUQ hKQC
  let c := inner Real (M.v : E3) (g p)
  have hcommonC (t : Real) (ht : t ∈ Icc (-(δ k)) (δ k)) :
      (ds k).A (c + t) ∩ C k = (ds k).B (c + t) ∩ C k := by
    ext x
    constructor
    · intro hx
      have hh := (hcommon k t ht).subset ⟨hx.1, hCN k hx.2⟩
      exact ⟨hh.1, hx.2⟩
    · intro hx
      have hh := (hcommon k t ht).symm.subset ⟨hx.1, hCN k hx.2⟩
      exact ⟨hh.1, hx.2⟩
  obtain ⟨L, _, hL, Φ0, hformula, hΦ00, hΦ0, hΦ0i, hΦ0fix, _, hΦ0match⟩ :=
    exists_two_parameter_matching_of_exterior_transport_and_anchor
      (fun t => (ds k).A (c + t)) (fun t => (ds k).B (c + t)) (C k)
      (Icc (-(δ k)) (δ k)) htime
      (by simpa only [add_zero] using hstationary k) hcommonC
      (Ψ k) R (hΨ k) (hΨi k) hR hRi
      (fun t x hx => hΨO k t x (hCO k hx))
      (fun u x hx => hRUQ u (hCUQ hx)) (K k) KQ (hK k) hKQ (hΨfix k) hRfix
      (by simpa only [add_zero] using hmove k) hR0
      (by simpa only [sub_eq_add_neg] using hmatch)
  let Φ (u z : Real) := Φ0 u (z - c)
  let W := O k ∩ UQ
  have hW : IsOpen W := (hO k).inter hUQ
  have hCW : C k ⊆ W := subset_inter (hCO k) hCUQ
  have hΦW (u z : Real) : EqOn (Φ u z) id W := by
    intro x hx
    change Φ0 u (z - c) x = x
    rw [hformula, hRUQ u hx.2]
    have hinv : (Ψ k (-τ)).symm x = x := by
      apply (Ψ k (-τ)).injective
      change Ψ k (-τ) ((Ψ k (-τ)).symm x) = Ψ k (-τ) x
      rw [Diffeomorph.apply_symm_apply, hΨO k (-τ) x hx.1]
    simpa only [id_eq, hinv] using hΨO k (-τ + u * (z - c - -τ)) x hx.1
  obtain ⟨ρ, hρ, _, _, hρsource, hρmodel, hU, hpatchU⟩ :=
    exists_terminal_spatially_protected_morse_square (ds k) (hsize k) hform
      (hδ k) (C k) (V k) (hpatchV k) (hfiber k) W hW hCW
  refine ⟨ds k, Or.inr ⟨δ k, hδ k, hδd k, hδη k, L, Φ, hL, ?_, ?_, ?_, ?_, ?_,
    ρ, hρ, Saddle.toE2 ⁻¹' W, hU, hρsource, hρmodel, hpatchU, ?_⟩⟩
  · intro z x
    exact hΦ00 (z - c) x
  · exact hΦ0.comp (show ContDiff Real ∞
      (fun q : Real × Real × E2 => (q.1, q.2.1 - c, q.2.2)) by fun_prop)
  · exact hΦ0i.comp (show ContDiff Real ∞
      (fun q : Real × Real × E2 => (q.1, q.2.1 - c, q.2.2)) by fun_prop)
  · intro u z x hx
    exact hΦ0fix u (z - c) x hx
  · intro z hz
    have ht : z - c ∈ Icc (-(δ k)) (δ k) := by constructor <;> linarith [hz.1, hz.2]
    simpa only [add_sub_cancel] using hΦ0match (z - c) ht
  · intro u y hy
    change Saddle.toE3 (Φ u (y 2) (Saddle.toE2 y)) (y 2) = y
    rw [hΦW u (y 2) hy]
    ext i
    fin_cases i <;> rfl

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
