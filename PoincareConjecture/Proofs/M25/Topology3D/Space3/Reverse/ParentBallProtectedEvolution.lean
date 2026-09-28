import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartTimeField
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockSmoothFlow
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ClockTracks
import PoincareConjecture.Proofs.M25.Topology3D.Services

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_protected_chart_evolution
    (e : OpenPartialHomeomorph (ℝ × E3) (ℝ × E3))
    (he : ContDiffOn ℝ ∞ e e.source)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (htime : ∀ p ∈ e.source, (e p).1 = p.1)
    (K M C : Set E3) (hM : IsCompact M) (hMK : M ⊆ K)
    (hC : IsClosed C)
    (hsource : Icc (-1 : ℝ) 2 ×ˢ K ⊆ e.source)
    (hstationary : ∀ x ∈ K \ M, ∀ t ∈ Icc (-1 : ℝ) 2,
      (e (t, x)).2 = (e (0, x)).2)
    (havoid : ∀ t ∈ Icc (-1 : ℝ) 2, ∀ x ∈ M, (e (t, x)).2 ∉ C) :
    ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      ∃ S : Set E3,
        ContDiff ℝ ∞ (fun p : ℝ × E3 => Φ p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × E3 => (Φ p.1).symm p.2) ∧
        (∀ y : E3, Φ 0 y = y) ∧
        (∀ t ∈ Ioo (-1 : ℝ) 2, ∀ x ∈ K,
          Φ t (e (0, x)).2 = (e (t, x)).2 ∧
          (Φ t).symm (e (t, x)).2 = (e (0, x)).2) ∧
        IsCompact S ∧ S ⊆ (Prod.snd '' e.target) \ C ∧
        (∀ t : ℝ, tsupport (fun y => Φ t y - y) ⊆ S) ∧
        (∀ t : ℝ, tsupport (fun y => (Φ t).symm y - y) ⊆ S) ∧
        (∀ t : ℝ, ∀ y ∉ S, Φ t y = y ∧ (Φ t).symm y = y) ∧
        ∀ t : ℝ, ∀ y ∈ C, Φ t y = y ∧ (Φ t).symm y = y := by
  let L : Set (ℝ × E3) := e '' (Icc (-1 : ℝ) 2 ×ˢ M)
  let U : Set (ℝ × E3) := e.target \ (univ ×ˢ C)
  have hMsource : Icc (-1 : ℝ) 2 ×ˢ M ⊆ e.source :=
    fun _ hp => hsource ⟨hp.1, hMK hp.2⟩
  have hL : IsCompact L :=
    (isCompact_Icc.prod hM).image_of_continuousOn (e.continuousOn.mono hMsource)
  have hU : IsOpen U := e.open_target.sdiff (isClosed_univ.prod hC)
  have hLU : L ⊆ U := by
    rintro p ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    exact ⟨e.map_source (hMsource ⟨ht, hx⟩),
      fun hmem => havoid t ht x hx hmem.2⟩
  obtain ⟨ρ, hρ, hρc, hρU, hnear, _hrange⟩ :=
    exists_compact_smooth_cutoff hL hU hLU
  have hρone (p : ℝ × E3) (hp : p ∈ L) : ρ p = 1 :=
    (eventually_nhdsSet_iff_forall.mp hnear p hp).self_of_nhds
  let V := chartTimeField e
  let W : ℝ × E3 → E3 := fun p => ρ p • V p
  have hV : ContDiffOn ℝ ∞ V U :=
    (chartTimeField_contDiffOn e he hei).mono sdiff_subset
  have hW : ContDiff ℝ ∞ W := contDiff_cutoff_smul hU ρ hρ hρU V hV
  have hWc : HasCompactSupport W := hρc.smul_right
  have hWs : tsupport W ⊆ U := (tsupport_smul_subset_left ρ V).trans hρU
  have hderiv (x : E3) (hx : x ∈ K) (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) :
      HasDerivAt (fun s => (e (s, x)).2) (W (t, (e (t, x)).2)) t := by
    have htx : (t, x) ∈ e.source := hsource ⟨Ioo_subset_Icc_self ht, hx⟩
    have hd : HasDerivAt (fun s => (e (s, x)).2) (V (t, (e (t, x)).2)) t :=
      chartTimeField_track e he htime t x htx
    by_cases hxM : x ∈ M
    · have hpL : (t, (e (t, x)).2) ∈ L :=
        ⟨(t, x), ⟨Ioo_subset_Icc_self ht, hxM⟩, Prod.ext (htime _ htx) rfl⟩
      have hWtrack : W (t, (e (t, x)).2) = V (t, (e (t, x)).2) := by
        change ρ (t, (e (t, x)).2) • V (t, (e (t, x)).2) = _
        rw [hρone _ hpL, one_smul]
      rw [hWtrack]
      exact hd
    · have hconstant : (fun s : ℝ => (e (s, x)).2) =ᶠ[𝓝 t]
          fun _ => (e (0, x)).2 := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
        exact hstationary x ⟨hx, hxM⟩ s (Ioo_subset_Icc_self hs)
      have hdzero : HasDerivAt (fun s : ℝ => (e (s, x)).2) 0 t :=
        (hasDerivAt_const t (e (0, x)).2).congr_of_eventuallyEq hconstant
      have hzero : V (t, (e (t, x)).2) = 0 := hd.unique hdzero
      have hWzero : W (t, (e (t, x)).2) = 0 := by
        change ρ (t, (e (t, x)).2) • V (t, (e (t, x)).2) = 0
        rw [hzero, smul_zero]
      rw [hWzero]
      exact hdzero
  obtain ⟨k, l, hk, hl⟩ := clockField_bounds W hW hWc
  let Φ : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
    fun t => clockEvolutionDiffeomorph W hk hl hW hWc 0 t
  let S : Set E3 := Prod.snd '' tsupport W
  have hSc : IsCompact S := hWc.isCompact.image continuous_snd
  have hSs : S ⊆ (Prod.snd '' e.target) \ C := by
    rintro y ⟨p, hp, rfl⟩
    refine ⟨⟨p, (hWs hp).1, rfl⟩, ?_⟩
    intro hyC
    exact (hWs hp).2 ⟨mem_univ _, hyC⟩
  have hfix (t : ℝ) (y : E3) (hy : y ∉ S) :
      Φ t y = y ∧ (Φ t).symm y = y := by
    have hz (s : ℝ) : W (s, y) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hp
      exact hy ⟨(s, y), hp, rfl⟩
    exact ⟨clockEvolution_eq_self W hk hl y hz 0 t,
      clockEvolution_eq_self W hk hl y hz t 0⟩
  refine ⟨Φ, S, ?_, ?_, ?_, ?_, hSc, hSs, ?_, ?_, hfix, ?_⟩
  · exact (clockEvolution_contDiff W hk hl hW hWc).comp
      (((contDiff_const (c := (0 : ℝ))).prodMk contDiff_fst).prodMk contDiff_snd)
  · exact (clockEvolution_contDiff W hk hl hW hWc).comp
      ((contDiff_fst.prodMk (contDiff_const (c := (0 : ℝ)))).prodMk contDiff_snd)
  · exact fun y => clockEvolution_self W hk hl 0 y
  · intro t ht x hx
    have htrack : Φ t (e (0, x)).2 = (e (t, x)).2 :=
      clockEvolution_tracks W hk hl (fun s => (e (s, x)).2)
        (by norm_num) (fun s hs => hderiv x hx s hs) ht
    refine ⟨htrack, ?_⟩
    rw [← htrack, (Φ t).symm_apply_apply]
  · intro t
    exact closure_minimal (clockEvolution_support_subset W hk hl 0 t) hSc.isClosed
  · intro t
    exact closure_minimal (clockEvolution_support_subset W hk hl t 0) hSc.isClosed
  · intro t y hy
    exact hfix t y (fun hyS => (hSs hyS).2 hy)

end PoincareConjecture.M25.Topology3D
