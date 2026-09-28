import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoCornerCoveredArcBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcInwardOrientation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_exists_two_corner_oriented_arc_bands
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ}
    (hinj : InjOn gamma (Icc 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) T, gamma t ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = gamma '' Icc 0 T ∪ K) (hfV : frontier V = frontier U)
    (r : Bool → ℝ) (hr : ∀ e, 0 < r e) (hrbound : ∀ e, r e ≤ T / 3)
    (H : Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (F : Bool → Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (positive vertical : Bool → Bool)
    (hsource : ∀ e i,
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e} ⊆ (F e i).source)
    (hF : ∀ e i, ContDiffOn ℝ ∞ (F e i) (F e i).source)
    (hFi : ∀ e i, ContDiffOn ℝ ∞ (F e i).symm (F e i).target)
    (hfirst : ∀ e i, ∀ s ∈ Icc (0 : ℝ) (r e),
      F e i (s, 0) = H e (sectorParameterEquiv 0 i (s, 0)))
    (hsecond : ∀ e i, ∀ s ∈ Icc (0 : ℝ) (r e),
      F e i (0, s) = H e (sectorParameterEquiv 0 i (0, s)))
    (hchord : ∀ e i, ∀ t : ℝ, F e i ((1 - t) * r e, t * r e) =
      (1 - t) • F e i (r e, 0) + t • F e i (0, r e))
    (hsector : ∀ e i,
      F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e} ⊆
        H e '' ((H e).source ∩ (sectorParameterEquiv 0 i) ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (haxis : ∀ e : Bool, ∀ s : ℝ,
      H e (if vertical e then (0, s) else (s, 0)) = gamma (if e then T - s else s))
    (htip : ∀ e : Bool,
      (if vertical e then ((0 : ℝ), r e) else (r e, 0)) ∈ (H e).source)
    {O : Set AnnulusCoordinates} (hO : IsOpen O)
    (hOarc : gamma '' Icc 0 T ⊆ O) :
    let C (e : Bool) := ⋃ i,
      ⋃ (_ : if positive e then i = (true, true) else i ≠ (true, true)),
        F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e}
    (∀ e, C e ⊆ closure U) → Disjoint (C false) (C true) →
    (∀ e : Bool, C e ∩ frontier U ⊆
      (fun s => gamma (if e then T - s else s)) '' Icc 0 (r e) ∪ K) →
    (∀ e : Bool, ∃ W : Set AnnulusCoordinates, IsOpen W ∧
      gamma (if e then T else 0) ∈ W ∧ W ∩ closure U ⊆ C e) →
    ∃ reversed : Bool,
      let g : ℝ → AnnulusCoordinates := fun t => gamma (if reversed then T - t else t)
      let r' (e : Bool) := r (if reversed then !e else e)
      ∃ (d : ℝ → AnnulusCoordinates) (n : ℕ) (c : Fin (n + 1) → ℝ)
        (L : Fin n → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
        (G : Fin n → OpenPartialHomeomorph ℝ ℝ) (f : Fin n → ℝ → ℝ) (ell : ℝ),
        0 < n ∧ StrictMono c ∧ c 0 = r' false ∧ c (Fin.last n) = T - r' true ∧ 0 < ell ∧
        ∃ B : ∀ i : Fin n,
          ObliqueBandFaces
            (collarParameterEquiv.trans (L i).symm).toHomeomorph.toOpenPartialHomeomorph
            (f i) (G i (c i.castSucc)) (G i (c i.succ))
            (L i (d (c i.castSucc))).1 (L i (d (c i.castSucc))).2
            (L i (d (c i.succ))).1 (L i (d (c i.succ))).2 ell ell,
          (∀ i, (B i).carrier ⊆ O) ∧
          (∀ i, (B i).lowerArc = g '' Icc (c i.castSucc) (c i.succ) ∧
            (B i).leftCut = segment ℝ (g (c i.castSucc))
              (g (c i.castSucc) + ell • d (c i.castSucc)) ∧
            (B i).rightCut = segment ℝ (g (c i.succ))
              (g (c i.succ) + ell • d (c i.succ)) ∧
            (B i).carrier ⊆ closure U ∧ (B i).carrier \ (B i).lowerArc ⊆ U) ∧
          (∀ i j : Fin n, i.succ < j.castSucc → Disjoint (B i).carrier (B j).carrier) ∧
          (∀ i j : Fin n, i.succ = j.castSucc →
            (B i).carrier ∩ (B j).carrier = segment ℝ (g (c i.succ))
              (g (c i.succ) + ell • d (c i.succ))) ∧
          (∀ i, (C false ∪ C true) ∩ (B i).carrier =
            (if c i.castSucc = r' false then (B i).leftCut else ∅) ∪
              (if c i.succ = T - r' true then (B i).rightCut else ∅)) ∧
          ∀ p ∈ Icc (0 : ℝ) T, ∃ W : Set AnnulusCoordinates,
            IsOpen W ∧ g p ∈ W ∧
              W ∩ closure U ⊆ (C false ∪ C true) ∪ ⋃ i, (B i).carrier := by
  classical
  intro C hsub hCC hcontact hcorner
  have hT : 0 < T := by linarith [hr false, hrbound false]
  obtain ⟨g0, hchoice, hg0, hi0, himage0, hreg0, havoid0, hray0⟩ :=
    m64Intrinsic_exists_global_arc_inward_orientation hg hT hinj hregular hK havoid
      hU hV hdisj hfU hfV
  obtain ⟨reversed, hgeq⟩ :
      ∃ reversed : Bool, g0 = fun t => gamma (if reversed then T - t else t) := by
    rcases hchoice with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  let flip (e : Bool) := if reversed then !e else e
  let g : ℝ → AnnulusCoordinates := fun t => gamma (if reversed then T - t else t)
  have hgeq : g0 = g := hgeq
  have hg' : ContDiff ℝ ∞ g := hgeq ▸ hg0
  have hi' : InjOn g (Icc 0 T) := hgeq ▸ hi0
  have himage : g '' Icc 0 T = gamma '' Icc 0 T := hgeq ▸ himage0
  have hreg : ∀ t ∈ Ioo (0 : ℝ) T, deriv g t ≠ 0 := hgeq ▸ hreg0
  have havoid' : ∀ t ∈ Ioo (0 : ℝ) T, g t ∉ K := hgeq ▸ havoid0
  have hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ z in 𝓝[>] (0 : ℝ),
      g t + z • quarterTurn (deriv g t) ∈ U := hgeq ▸ hray0
  have hparam (e : Bool) (s : ℝ) :
      gamma (if flip e then T - s else s) = g (if e then T - s else s) := by
    cases reversed <;> cases e <;> simp [g, flip]
  have haxis' (e : Bool) (s : ℝ) :
      H (flip e) (if vertical (flip e) then (0, s) else (s, 0)) =
        g (if e then T - s else s) := (haxis (flip e) s).trans (hparam e s)
  have hfront : frontier U = g '' Icc 0 T ∪ K := by rw [himage]; exact hfU
  have hcontact' (e : Bool) :
      C (flip e) ∩ frontier U ⊆
        (fun s => g (if e then T - s else s)) '' Icc 0 (r (flip e)) ∪ K := by
    have heq : (fun s => gamma (if flip e then T - s else s)) =
        (fun s => g (if e then T - s else s)) := funext (hparam e)
    simpa only [heq] using hcontact (flip e)
  have hcorner' (e : Bool) : ∃ W : Set AnnulusCoordinates, IsOpen W ∧
      g (if e then T else 0) ∈ W ∧ W ∩ closure U ⊆ C (flip e) := by
    obtain ⟨W, hW, hpW, hcover⟩ := hcorner (flip e)
    refine ⟨W, hW, ?_, hcover⟩
    have heq : gamma (if flip e then T else 0) = g (if e then T else 0) := by
      cases reversed <;> cases e <;> simp [g, flip]
    exact heq ▸ hpW
  have hCC' : Disjoint (C (flip false)) (C (flip true)) := by
    cases reversed
    · exact hCC
    · exact hCC.symm
  have hunion : C (flip false) ∪ C (flip true) = C false ∪ C true := by
    cases reversed
    · rfl
    · exact union_comm _ _
  have result := m64Intrinsic_exists_two_corner_covered_arc_bands hg' hi' hreg hK havoid'
    hU hV hdisj hfront hfV hray (fun e => r (flip e)) (fun e => hr (flip e))
    (fun e => hrbound (flip e)) (fun e => H (flip e)) (fun e => F (flip e))
    (fun e => positive (flip e)) (fun e => vertical (flip e))
    (fun e => hsource (flip e)) (fun e => hF (flip e)) (fun e => hFi (flip e))
    (fun e => hfirst (flip e)) (fun e => hsecond (flip e)) (fun e => hchord (flip e))
    (fun e => hsector (flip e)) haxis' (fun e => htip (flip e))
    hO (by rw [himage]; exact hOarc) (fun e => hsub (flip e)) hCC' hcontact' hcorner'
  refine ⟨reversed, ?_⟩
  dsimp only [C] at hunion
  simpa only [hunion] using result

end PoincareConjecture
