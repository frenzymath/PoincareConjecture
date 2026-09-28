import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_CompactnessFeedEndpoint
import PoincareConjecture.Proofs.M44.Mathlib.CompactSmoothConvergence
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SpatialJets












set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M44

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]




theorem tendsto_spatialJet_of_compactSmooth
    {fseq : ℕ → ℝ × E → V} {f : ℝ × E → V} {U : Set (ℝ × E)}
    (h : CompactSmoothConvergenceOn fseq f atTop U)
    {p : ℝ × E} (hp : p ∈ U) (m : ℕ) :
    Tendsto (fun k => iteratedFDeriv ℝ m (fun x => fseq k (p.1, x)) p.2) atTop
      (𝓝 (iteratedFDeriv ℝ m (fun x => f (p.1, x)) p.2)) := by
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := V) (fun _ : Fin m => ContinuousLinearMap.inr ℝ ℝ E)
  have hfull := (h.jets m {p} isCompact_singleton
    (singleton_subset_iff.mpr hp)).tendsto_at (mem_singleton p)
  have hlimit := P.continuous.continuousAt.tendsto.comp hfull
  have hread : iteratedFDeriv ℝ m (fun x => f (p.1, x)) p.2 =
      P (iteratedFDeriv ℝ m f p) := by
    ext v
    exact Poincare.Analysis.iteratedFDeriv_spatial_slice f
      (h.smooth.contDiffAt (h.isOpen.mem_nhds hp)) m v
  rw [← hread] at hlimit
  apply hlimit.congr'
  filter_upwards [h.eventually_smooth {p} isCompact_singleton
    (singleton_subset_iff.mpr hp)] with k hk
  ext v
  exact (Poincare.Analysis.iteratedFDeriv_spatial_slice (fseq k)
    (hk p (mem_singleton p)) m v).symm



noncomputable def birthExtendedCoefficients (b0 : E → V) (b : ℝ × E → V) :
    ℝ × E → V := by
  classical
  exact fun p => if p.1 = 0 then b0 p.2 else b p

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] in


theorem birthExtendedCoefficients_zero (b0 : E → V) (b : ℝ × E → V) :
    (fun x => birthExtendedCoefficients b0 b (0, x)) = b0 := by
  funext x
  simp [birthExtendedCoefficients]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] in


theorem birthExtendedCoefficients_interior (b0 : E → V) (b : ℝ × E → V) (T : ℝ) :
    EqOn (birthExtendedCoefficients b0 b) b (Ioo 0 T ×ˢ univ) := by
  intro p hp
  exact if_neg hp.1.1.ne'




theorem birthExtendedCoefficients_spatial_smooth
    {b0 : E → V} {b : ℝ × E → V} {T : ℝ}
    (hb0 : ContDiff ℝ ∞ b0) (hb : ContDiffOn ℝ ∞ b (Ioo 0 T ×ˢ univ)) :
    ∀ t ∈ Ico 0 T, ContDiffOn ℝ ∞
      (fun x => birthExtendedCoefficients b0 b (t, x)) univ := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with hzero | hpos
  · subst t
    rw [birthExtendedCoefficients_zero]
    exact hb0.contDiffOn
  · have hslice : ContDiffOn ℝ ∞ (fun x : E => b (t, x)) univ :=
      hb.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun x _ => (show (t, x) ∈ Ioo 0 T ×ˢ (univ : Set E) from
        ⟨⟨hpos, ht.2⟩, mem_univ x⟩))
    simpa only [birthExtendedCoefficients, if_neg hpos.ne'] using hslice





theorem continuousOn_birthExtended_spatialJets [ProperSpace E]
    {fseq : ℕ → ℝ × E → V} {b : ℝ × E → V} {b0 : E → V}
    {T : ℝ} (hT : 0 < T) (hb0 : ContDiff ℝ ∞ b0)
    (hconv : CompactSmoothConvergenceOn fseq b atTop (Ioo 0 T ×ˢ univ))
    (hbirth : ∀ m : ℕ, ∀ x : E,
      Tendsto (fun k => iteratedFDeriv ℝ m (fun y => fseq k (0, y)) x) atTop
        (𝓝 (iteratedFDeriv ℝ m b0 x)))
    (hmodulus : ∀ m : ℕ, ∀ K : Set E, IsCompact K → ∃ L : ℝ, 0 ≤ L ∧
      ∀ t ∈ Ioo 0 T, ∀ x ∈ K, ∀ᶠ k in atTop,
        ‖iteratedFDeriv ℝ m (fun y => fseq k (t, y)) x -
          iteratedFDeriv ℝ m (fun y => fseq k (0, y)) x‖ ≤ L * t) :
    ∀ m : ℕ, ContinuousOn
      (fun p => iteratedFDeriv ℝ m
        (fun x => birthExtendedCoefficients b0 b (p.1, x)) p.2) (Ico 0 T ×ˢ univ) := by
  have hsmooth : ContDiffOn ℝ ∞ (birthExtendedCoefficients b0 b) (Ioo 0 T ×ˢ univ) :=
    hconv.smooth.congr (birthExtendedCoefficients_interior b0 b T)
  intro m
  have hright (x : E) : ContinuousWithinAt
      (fun p : ℝ × E => iteratedFDeriv ℝ m
        (fun y => birthExtendedCoefficients b0 b (p.1, y)) p.2) (Ici 0 ×ˢ univ) (0, x) := by
    apply continuousWithinAt_birth_of_uniform_modulus hT isOpen_univ
      (fseq := fun k p => iteratedFDeriv ℝ m (fun y => fseq k (p.1, y)) p.2)
    · change ContinuousOn (iteratedFDeriv ℝ m
        (fun y => birthExtendedCoefficients b0 b (0, y))) univ
      rw [birthExtendedCoefficients_zero]
      exact (hb0.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
    · intro y _hy
      simpa only [birthExtendedCoefficients_zero] using hbirth m y
    · intro t ht y _hy
      simpa only [birthExtendedCoefficients, if_neg ht.1.ne'] using
        tendsto_spatialJet_of_compactSmooth hconv
          (show (t, y) ∈ Ioo 0 T ×ˢ (univ : Set E) from ⟨ht, mem_univ y⟩) m
    · intro K hK _hKU
      exact hmodulus m K hK
    · exact mem_univ x
  have hinterior := (contDiffOn_spatialJet_within hsmooth
    isOpen_Ioo.uniqueDiffOn isOpen_univ m).continuousOn
  rintro ⟨t, x⟩ ht
  rcases eq_or_lt_of_le ht.1.1 with hzero | hpos
  · change 0 = t at hzero
    subst t
    exact (hright x).mono (prod_mono (fun _ hs => hs.1) Subset.rfl)
  · exact (hinterior.continuousAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨⟨hpos, ht.1.2⟩, ht.2⟩)).continuousWithinAt

end PoincareConjecture.M44
