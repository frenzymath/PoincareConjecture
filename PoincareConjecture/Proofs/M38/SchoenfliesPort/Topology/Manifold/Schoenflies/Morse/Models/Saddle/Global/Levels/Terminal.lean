import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Levels.Actual
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.Saddle.Flattening







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereMorseReduction

open SaddleLevel Saddle.Levels

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem exists_terminal_flattened_band_level_sets
    {f : S2 → E3} (M : SphereMorseReduction f)
    {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    (hcaps : P.PreservesCaps) {p : S2} (hp : p ∈ P.core)
    (hc : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (M.v : E3) (g q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    {ε : Real} (hε : 0 < ε) :
    let h := fun q => inner Real (M.v : E3) (g q)
    ∃ (r δ : Real) (a b : Fin 2 → Real)
        (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
        (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
        (A B : Fin 2 → Real → Real),
      0 < r ∧ r < ε ∧ closedSquare r ⊆ e.source ∧
      0 < δ ∧ δ < ε ∧ δ < r^2 ∧
      (∀ y, inner Real (M.v : E3) (D y) = inner Real (M.v : E3) y) ∧
      (∀ y, inner Real (M.v : E3) y = inner Real (M.v : E3) (g p) → D y = y) ∧
      ∀ t ∈ Icc (-δ) δ,
        (∀ i, ContinuousAt (A i) t ∧ ContinuousAt (B i) t ∧
          a i < A i t ∧ A i t < B i t ∧ B i t < b i) ∧
        (D ∘ g) '' (h ⁻¹' {h p + t}) =
          (D ∘ g ∘ e) '' (closedSquare r ∩ {x : E2 | -(x 0)^2 + (x 1)^2 = t}) ∪
          (⋃ i, (fun s => g (F i (s, 0)) + t • (M.v : E3)) '' Icc (a i) (b i)) ∧
        (D ∘ g) '' ((h ⁻¹' {h p + t}) \ e '' openSquare r) =
          ⋃ i, (fun s => g (F i (s, 0)) + t • (M.v : E3)) ''
            Icc (A i t) (B i t) := by
  dsimp only
  let h := fun q => inner Real (M.v : E3) (g q)
  obtain ⟨r, w, η, a, b, F, hr, hrε, hrs, hw, hη, hηw, hηε, hab,
      hFs, hF, hFi, hheight, hdisjoint, hcore, hband,
      ⟨a₀, b₀, hchain, hcentral, hends⟩, hpair,
      K, V, D, hK, hKband, hV, hpV, hDV, hDK, hDh, hDc, hflat⟩ :=
    M.exists_terminal_saddle_band_flattening hg P hP hcaps hp hc e he0 hep he hei
      hform hε
  have hrect (i : Fin 2) : Icc (a i) (b i) ×ˢ Icc (-η) η ⊆ (F i).source := by
    intro z hz
    rw [hFs i]
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  obtain ⟨δ, L, A, B, hδ, hδη, hδr, hL, hABzero, hrecut⟩ :=
    exists_recut_exterior_strips e hr hrs hform F a b a₀ b₀ hη hchain hrect
      hheight hdisjoint hcentral hends hband
  refine ⟨r, δ, a, b, F, D, A, B, hr, hrε, hrs, hδ, hδη.trans hηε, hδr, hDh, ?_⟩
  refine ⟨hDc, ?_⟩
  intro t ht
  have htη : t ∈ Icc (-η) η := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨hAB, hexterior⟩ := hrecut t ht
  refine ⟨fun i => ⟨(hAB i).1, (hAB i).2.1, (hAB i).2.2.1,
    (hAB i).2.2.2.1, (hAB i).2.2.2.2.1⟩, ?_, ?_⟩
  · exact flattened_fiber_eq_patch_union_strip_slices g D (M.v : E3) e hform hw hηw hrs
      hFs hheight hband hflat htη
  · exact flattened_exterior_eq_recut_strip_slices g D (M.v : E3) e F a b
      (fun i => A i t) (fun i => B i t)
      (fun i => (hAB i).2.2.1.le) (fun i => (hAB i).2.2.2.2.1.le)
      hexterior hflat htη

end Poincare.Manifold.Schoenflies.SphereMorseReduction

end

end M38Schoenflies
