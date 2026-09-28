import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Levels.Terminal

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel Saddle.Levels
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
local notation "IR2" => 𝓘(Real, Real × Real)

theorem exists_terminal_flattened_strips
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
    ∃ (r w η δ : Real) (a b a₀ b₀ : Fin 2 → Real)
        (F : Fin 2 → OpenPartialHomeomorph (Real × Real) S2)
        (K V : Set E3) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
        (L : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2)) (A B : Fin 2 → Real → Real),
      0 < r ∧ r < ε ∧ closedSquare r ⊆ e.source ∧
      0 < w ∧ 0 < η ∧ η < w ∧ η < ε ∧ (∀ i, a i < b i) ∧
      (∀ i, (F i).source = Ioo (a i - w) (b i + w) ×ˢ Ioo (-w) w) ∧
      (∀ i, ContMDiffOn IR2 (𝓡 2) ∞ (F i) (F i).source) ∧
      (∀ i, ContMDiffOn (𝓡 2) IR2 ∞ (F i).symm (F i).target) ∧
      (∀ i z, z ∈ (F i).source → h (F i z) = h p + z.2) ∧
      Pairwise (fun i j => Disjoint (F i).target (F j).target) ∧
      h ⁻¹' Icc (h p - η) (h p + η) ⊆ interior P.core ∧
      h ⁻¹' Icc (h p - η) (h p + η) ⊆ e '' openSquare r ∪
        ⋃ i, F i '' (Icc (a i) (b i) ×ˢ Icc (-η) η) ∧
      (∀ i, a i < a₀ i ∧ a₀ i < b₀ i ∧ b₀ i < b i) ∧
      (⋃ i, F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        (h ⁻¹' {h p}) \ e '' openSquare r ∧
      (∀ i, range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
          (F i '' (Icc (a₀ i) (b₀ i) ×ˢ ({0} : Set Real))) =
        {F i (a₀ i, 0), F i (b₀ i, 0)}) ∧
      ((∀ i j : Fin 2 × Fin 2,
        e (contact r i) ∈ connectedComponentIn ((h ⁻¹' {h p}) \ e '' openSquare r)
          (e (contact r j)) ↔ i.1 = j.1) ∨
       (∀ i j : Fin 2 × Fin 2,
        e (contact r i) ∈ connectedComponentIn ((h ⁻¹' {h p}) \ e '' openSquare r)
          (e (contact r j)) ↔ i.2 = j.2)) ∧
      IsCompact K ∧ K ⊆ {x | |inner Real (M.v : E3) x - h p| ≤ ε} ∧
      IsOpen V ∧ g p ∈ V ∧ EqOn D id V ∧
      (∀ x ∉ K, D x = x) ∧
      (∀ x, inner Real (M.v : E3) (D x) = inner Real (M.v : E3) x) ∧
      (∀ x, inner Real (M.v : E3) x = h p → D x = x) ∧
      (∀ i t, t ∈ Icc (-η) η → ∀ s ∈ Icc (a i) (b i),
        D (g (F i (s, t))) = g (F i (s, 0)) + t • (M.v : E3)) ∧
      0 < δ ∧ δ < η ∧ δ < ε ∧ δ < r ^ 2 ∧
      (∀ k, F k.1 (stripEndpoint a₀ b₀ k, 0) = e (contact r (L k))) ∧
      (∀ i, A i 0 = a₀ i ∧ B i 0 = b₀ i) ∧
      ∀ t ∈ Icc (-δ) δ,
        (∀ i, ContinuousAt (A i) t ∧ ContinuousAt (B i) t ∧
          a i < A i t ∧ A i t < B i t ∧ B i t < b i ∧
          (Icc (A i t) (B i t) ×ˢ ({t} : Set Real) ⊆ (F i).source) ∧
          F i (A i t, t) = e (movingContact r t (L (i, 0))) ∧
          F i (B i t, t) = e (movingContact r t (L (i, 1))) ∧
          (∀ s ∈ Icc (a i) (b i),
            F i (s, t) ∉ e '' openSquare r ↔ s ∈ Icc (A i t) (B i t))) ∧
        ((h ⁻¹' {h p + t}) \ e '' openSquare r) =
          ⋃ i, F i '' (Icc (A i t) (B i t) ×ˢ ({t} : Set Real)) ∧
        (D ∘ g) '' (h ⁻¹' {h p + t}) =
          (D ∘ g ∘ e) '' (closedSquare r ∩ {x : E2 | -(x 0)^2 + (x 1)^2 = t}) ∪
          (⋃ i, (fun s => g (F i (s, 0)) + t • (M.v : E3)) '' Icc (a i) (b i)) ∧
        (D ∘ g) '' ((h ⁻¹' {h p + t}) \ e '' openSquare r) =
          ⋃ i, (fun s => g (F i (s, 0)) + t • (M.v : E3)) ''
            Icc (A i t) (B i t) := by
  dsimp only
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
  refine ⟨r, w, η, δ, a, b, a₀, b₀, F, K, V, D, L, A, B,
    hr, hrε, hrs, hw, hη, hηw, hηε, hab, hFs, hF, hFi, hheight, hdisjoint,
    hcore, hband, hchain, hcentral, hends, hpair, hK, hKband, hV, hpV, hDV,
    hDK, hDh, hDc, hflat, hδ, hδη, hδη.trans hηε, hδr, hL, hABzero, ?_⟩
  intro t ht
  have htη : t ∈ Icc (-η) η := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨hAB, hexterior⟩ := hrecut t ht
  refine ⟨hAB, hexterior, ?_, ?_⟩
  · exact flattened_fiber_eq_patch_union_strip_slices g D (M.v : E3) e hform hw hηw hrs
      hFs hheight hband hflat htη
  · exact flattened_exterior_eq_recut_strip_slices g D (M.v : E3) e F a b
      (fun i => A i t) (fun i => B i t)
      (fun i => (hAB i).2.2.1.le) (fun i => (hAB i).2.2.2.2.1.le)
      hexterior hflat htη

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
