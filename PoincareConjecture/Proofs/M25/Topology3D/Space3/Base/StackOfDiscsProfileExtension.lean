import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockSmoothFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockTracks










set_option autoImplicit false

open Set Filter
open scoped ContDiff Manifold NNReal Topology

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]



theorem exists_compact_timeField_extension_away
    {K U : Set (ℝ × E)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (V : ℝ × E → E) (hV : ContDiffOn ℝ ∞ V U)
    {N : Set E} (hN : IsOpen N)
    (hzero : ∀ t y, y ∈ N → (t, y) ∈ U → V (t, y) = 0) :
    ∃ W : ℝ × E → E, ContDiff ℝ ∞ W ∧ HasCompactSupport W ∧
      tsupport W ⊆ U \ (univ ×ˢ N) ∧
      (∀ᶠ p in 𝓝ˢ K, W p = V p) ∧
      ∀ t y, y ∈ N → W (t, y) = 0 := by
  obtain ⟨ρ, hρ, hρc, hρU, hnear, _⟩ :=
    exists_compact_smooth_cutoff hK hU hKU
  let W : ℝ × E → E := fun p => ρ p • V p
  have hWU : tsupport W ⊆ U := (tsupport_smul_subset_left ρ V).trans hρU
  have hWN (t : ℝ) (y : E) (hy : y ∈ N) : W (t, y) = 0 := by
    by_cases hρzero : ρ (t, y) = 0
    · simp only [W, hρzero, zero_smul]
    · change ρ (t, y) • V (t, y) = 0
      rw [hzero t y hy (hρU (subset_tsupport ρ hρzero)), smul_zero]
  have hWaway : tsupport W ⊆ (univ ×ˢ N)ᶜ := by
    apply closure_minimal _ (isOpen_univ.prod hN).isClosed_compl
    intro p hp hpN
    exact hp (hWN p.1 p.2 hpN.2)
  refine ⟨W, contDiff_cutoff_smul hU ρ hρ hρU V hV, hρc.smul_right,
    fun p hp => ⟨hWU hp, hWaway hp⟩, ?_, hWN⟩
  filter_upwards [hnear] with p hp
  simp only [W, hp, one_smul]



theorem exists_ambient_evolution_of_localField_away
    {K U : Set (ℝ × E)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (V : ℝ × E → E) (hV : ContDiffOn ℝ ∞ V U)
    {N : Set E} (hN : IsOpen N)
    (hzero : ∀ t y, y ∈ N → (t, y) ∈ U → V (t, y) = 0)
    {Q : Type*} (γ : ℝ → Q → E) {a b r : ℝ} (hr : r ∈ Ioo a b)
    (htracks : ∀ q t, t ∈ Ioo a b → (t, γ t q) ∈ K)
    (hderiv : ∀ q t, t ∈ Ioo a b →
      HasDerivAt (fun z => γ z q) (V (t, γ t q)) t) :
    ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∃ C : Set E,
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (Φ p.1).symm p.2) ∧
      (∀ x, Φ r x = x) ∧
      (∀ q t, t ∈ Ioo a b → Φ t (γ r q) = γ t q) ∧
      IsCompact C ∧ C ⊆ (Prod.snd '' U) \ N ∧
      (∀ t, tsupport (fun x => Φ t x - x) ⊆ C) ∧
      (∀ t, tsupport (fun x => (Φ t).symm x - x) ⊆ C) ∧
      (∀ t x, x ∉ C → Φ t x = x ∧ (Φ t).symm x = x) ∧
      ∀ t x, x ∈ N → Φ t x = x ∧ (Φ t).symm x = x := by
  obtain ⟨W, hW, hWc, hWs, hnear, hWN⟩ :=
    exists_compact_timeField_extension_away hK hU hKU V hV hN hzero
  have hagree (p : ℝ × E) (hp : p ∈ K) : W p = V p :=
    (eventually_nhdsSet_iff_forall.mp hnear p hp).self_of_nhds
  obtain ⟨k, l, hk, hl⟩ := clockField_bounds W hW hWc
  let Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
    fun t => clockEvolutionDiffeomorph W hk hl hW hWc r t
  let C : Set E := Prod.snd '' tsupport W
  have hCc : IsCompact C := hWc.isCompact.image continuous_snd
  have hCs : C ⊆ (Prod.snd '' U) \ N := by
    rintro x ⟨p, hp, rfl⟩
    refine ⟨⟨p, (hWs hp).1, rfl⟩, ?_⟩
    intro hpN
    exact (hWs hp).2 ⟨mem_univ _, hpN⟩
  have hfix (t : ℝ) (x : E) (hx : x ∉ C) :
      Φ t x = x ∧ (Φ t).symm x = x := by
    have hz (s : ℝ) : W (s, x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hp
      exact hx ⟨(s, x), hp, rfl⟩
    exact ⟨clockEvolution_eq_self W hk hl x hz r t,
      clockEvolution_eq_self W hk hl x hz t r⟩
  refine ⟨Φ, C, ?_, ?_, ?_, ?_, hCc, hCs, ?_, ?_, hfix, ?_⟩
  · exact (clockEvolution_contDiff W hk hl hW hWc).comp
      (((contDiff_const (c := r)).prodMk contDiff_fst).prodMk contDiff_snd)
  · exact (clockEvolution_contDiff W hk hl hW hWc).comp
      ((contDiff_fst.prodMk (contDiff_const (c := r))).prodMk contDiff_snd)
  · exact fun x => clockEvolution_self W hk hl r x
  · intro q t ht
    apply clockEvolution_tracks W hk hl (fun z => γ z q) hr ?_ ht
    intro z hz
    rw [hagree (z, γ z q) (htracks q z hz)]
    exact hderiv q z hz
  · intro t
    exact closure_minimal (clockEvolution_support_subset W hk hl r t) hCc.isClosed
  · intro t
    exact closure_minimal (clockEvolution_support_subset W hk hl t r) hCc.isClosed
  · intro t x hx
    exact ⟨clockEvolution_eq_self W hk hl x (fun s => hWN s x hx) r t,
      clockEvolution_eq_self W hk hl x (fun s => hWN s x hx) t r⟩

end PoincareConjecture.M25.Topology3D
