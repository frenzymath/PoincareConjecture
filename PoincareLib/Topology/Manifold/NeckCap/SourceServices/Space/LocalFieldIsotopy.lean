import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Space.ClockSmoothFlow
import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Space.ClockTracks
import PoincareLib.Topology.Manifold.NeckCap.SourceServices.Space.FieldLocalization

/-!+# Compact ambient isotopies from local velocity fields

A local smooth field near compact prescribed tracks extends to a smooth
ambient isotopy following those tracks. A linear coordinate annihilating
the local field remains fixed throughout the isotopy. This is the ODE
assembly for the restricted horizontal moves in Hatcher, Notes on Basic
3-Manifold Topology, Lemma 1.2, pp. 2-3.

The construction of the local field from geometric tube coordinates is
a separate input; no general isotopy-extension theorem is assumed.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Manifold NNReal Topology

namespace PoincareMT.M25.Topology3D

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Any linear coordinate annihilating a time-dependent field is
preserved by its evolution; Hatcher's horizontal isotopies, Lemma 1.2. -/
theorem clockEvolution_preserves_linear [CompleteSpace E]
    (V : ℝ × E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K (clockField V)) (hL : ∀ p, ‖clockField V p‖ ≤ L)
    (A : E →L[ℝ] F) (hA : ∀ p, A (V p) = 0) (s t : ℝ) (x : E) :
    A (clockEvolution V hK hL s t x) = A x :=
  boundedFlow_preserves_linear (clockField V) hK hL
    (A.comp (ContinuousLinearMap.snd ℝ ℝ E)) hA (s, x) (t - s)

/-- A smooth local field near a compact family of solution tracks
extends to a global ambient isotopy, retaining a common compact support
and every specified linear first integral; Hatcher, Lemma 1.2, pp. 2-3. -/
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

end PoincareMT.M25.Topology3D
