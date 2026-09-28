import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockSmoothFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockTracks
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization

set_option autoImplicit false

open Set Filter
open scoped ContDiff Manifold NNReal Topology

namespace PoincareConjecture.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem clockEvolution_preserves_linear [CompleteSpace E]
    (V : ℝ × E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K (clockField V)) (hL : ∀ p, ‖clockField V p‖ ≤ L)
    (A : E →L[ℝ] F) (hA : ∀ p, A (V p) = 0) (s t : ℝ) (x : E) :
    A (clockEvolution V hK hL s t x) = A x :=
  boundedFlow_preserves_linear (clockField V) hK hL
    (A.comp (ContinuousLinearMap.snd ℝ ℝ E)) hA (s, x) (t - s)

theorem exists_ambient_isotopy_of_localField [FiniteDimensional ℝ E]
    {Q : Type*} {K U : Set (ℝ × E)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (V : ℝ × E → E) (hV : ContDiffOn ℝ ∞ V U)
    (A : E →L[ℝ] F) (hA : ∀ p ∈ U, A (V p) = 0)
    (c : ℝ → Q → E) {a b s : ℝ} (hs : s ∈ Ioo a b)
    (htracks : ∀ q t, t ∈ Ioo a b → (t, c t q) ∈ K)
    (hc : ∀ q t, t ∈ Ioo a b → HasDerivAt (fun z => c z q) (V (t, c t q)) t) :
    ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      (∀ x, Φ s x = x) ∧
      (∀ q t, t ∈ Ioo a b → Φ t (c s q) = c t q) ∧
      (∃ C : Set E, IsCompact C ∧ C ⊆ Prod.snd '' U ∧ ∀ t x, x ∉ C → Φ t x = x) ∧
      ∀ t x, A (Φ t x) = A x := by
  obtain ⟨W, hW, hWs, hWsupport, hnear, hWA⟩ :=
    exists_compactField_extension_preserving hK hU hKU V hV (fun _ => A) hA
  have hagree (p : ℝ × E) (hp : p ∈ K) : W p = V p :=
    (eventually_nhdsSet_iff_forall.mp hnear p hp).self_of_nhds
  obtain ⟨k, l, hk, hl⟩ := clockField_bounds W hW hWs
  let Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
    fun t => clockEvolutionDiffeomorph W hk hl hW hWs s t
  refine ⟨Φ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (clockEvolution_contDiff W hk hl hW hWs).comp
      (((contDiff_const (c := s)).prodMk contDiff_fst).prodMk contDiff_snd)
  · intro x
    exact clockEvolution_self W hk hl s x
  · intro q t ht
    apply clockEvolution_tracks W hk hl (fun z => c z q) hs ?_ ht
    intro z hz
    rw [hagree (z, c z q) (htracks q z hz)]
    exact hc q z hz
  · refine ⟨Prod.snd '' tsupport W, hWs.isCompact.image continuous_snd,
      image_mono hWsupport, ?_⟩
    intro t x hx
    apply clockEvolution_eq_self W hk hl x ?_ s t
    intro u
    apply image_eq_zero_of_notMem_tsupport
    intro hp
    exact hx ⟨(u, x), hp, rfl⟩
  · intro t x
    exact clockEvolution_preserves_linear W hk hl A hWA s t x

end PoincareConjecture.M25.Topology3D
