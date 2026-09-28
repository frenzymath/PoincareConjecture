import PoincareConjecture.Proofs.M44.Mathlib.CompactTimeLimit
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_ClosedTimeJets
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44




theorem continuousOn_birth_spatialJet
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {B T : ℝ} (hT : 0 < T) (hTB : T < B)
    (F : RicciFlow n M (Ico 0 B))
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (m : ℕ) :
    ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      iteratedFDeriv ℝ m ((F.metric p.1).pullbackCoefficients e) p.2) (Icc 0 T ×ˢ U) := by
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
    (show Icc (0 : ℝ) T ⊆ Ico 0 B from fun _ hs => ⟨hs.1, hs.2.trans_lt hTB⟩)
    ordConnected_Icc (Icc_infinite hT).nontrivial
  exact continuousOn_pullback_spatialJet hT G hU he m




theorem continuousWithinAt_birth_of_compact_uniform
    {X Y : Type*} [MetricSpace X] [ProperSpace X] [PseudoMetricSpace Y]
    {f : ℝ × X → Y} {U : Set X} (hU : IsOpen U)
    (hslice : ContinuousOn (fun x => f (0, x)) U)
    (hlim : ∀ K : Set X, IsCompact K → K ⊆ U → ∀ eta : ℝ, 0 < eta →
      ∃ d : ℝ, 0 < d ∧ ∀ t : ℝ, 0 < t → t < d →
        ∀ x ∈ K, dist (f (t, x)) (f (0, x)) < eta)
    {x : X} (hx : x ∈ U) :
    ContinuousWithinAt f (Ici 0 ×ˢ U) (0, x) := by
  have hleft : ContinuousWithinAt (fun p : ℝ × X => f (-p.1, p.2))
      (Iic 0 ×ˢ U) (0, x) := by
    apply Poincare.continuousWithinAt_time_left_of_compact_uniform hU
      (by simpa only [neg_zero] using hslice) ?_ hx
    intro K hK hKU eta heta
    obtain ⟨d, hd, hbound⟩ := hlim K hK hKU eta heta
    refine ⟨d, hd, fun t ht ht0 y hy => ?_⟩
    simpa only [neg_zero] using hbound (-t) (by linarith) (by linarith) y hy
  have hreflect : Continuous (fun p : ℝ × X => (-p.1, p.2)) :=
    continuous_fst.neg.prodMk continuous_snd
  have hmap : MapsTo (fun p : ℝ × X => (-p.1, p.2)) (Ici 0 ×ˢ U) (Iic 0 ×ˢ U) := by
    intro p hp
    change -p.1 ≤ 0 ∧ p.2 ∈ U
    exact ⟨neg_nonpos.mpr hp.1, hp.2⟩
  have hleft' : ContinuousWithinAt (fun p : ℝ × X => f (-p.1, p.2))
      (Iic 0 ×ˢ U) (-0, x) := by simpa only [neg_zero] using hleft
  simpa only [Function.comp_def, neg_neg] using
    hleft'.comp (f := fun p : ℝ × X => (-p.1, p.2)) (x := (0, x))
      hreflect.continuousWithinAt hmap





theorem continuousWithinAt_birth_of_uniform_modulus
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {fseq : ℕ → ℝ × E → V} {f : ℝ × E → V} {U : Set E}
    {T : ℝ} (hT : 0 < T) (hU : IsOpen U)
    (hslice : ContinuousOn (fun x => f (0, x)) U)
    (hbirth : ∀ x ∈ U, Tendsto (fun k => fseq k (0, x)) atTop (𝓝 (f (0, x))))
    (hinterior : ∀ t ∈ Ioo 0 T, ∀ x ∈ U,
      Tendsto (fun k => fseq k (t, x)) atTop (𝓝 (f (t, x))))
    (hmodulus : ∀ K : Set E, IsCompact K → K ⊆ U → ∃ L : ℝ, 0 ≤ L ∧
      ∀ t ∈ Ioo 0 T, ∀ x ∈ K, ∀ᶠ k in atTop,
        ‖fseq k (t, x) - fseq k (0, x)‖ ≤ L * t)
    {x : E} (hx : x ∈ U) :
    ContinuousWithinAt f (Ici 0 ×ˢ U) (0, x) := by
  apply continuousWithinAt_birth_of_compact_uniform hU hslice ?_ hx
  intro K hK hKU eta heta
  obtain ⟨L, hL, hbound⟩ := hmodulus K hK hKU
  have hL1 : 0 < L + 1 := by linarith
  refine ⟨min T (eta / (L + 1)), lt_min hT (div_pos heta hL1), ?_⟩
  intro t ht0 htd y hy
  have ht : t ∈ Ioo 0 T := ⟨ht0, htd.trans_le (min_le_left _ _)⟩
  have hlimit : ‖f (t, y) - f (0, y)‖ ≤ L * t :=
    le_of_tendsto (((hinterior t ht y (hKU hy)).sub (hbirth y (hKU hy))).norm)
      (hbound t ht y hy)
  rw [dist_eq_norm]
  calc
    ‖f (t, y) - f (0, y)‖ ≤ L * t := hlimit
    _ ≤ (L + 1) * t := mul_le_mul_of_nonneg_right (by linarith) ht0.le
    _ < eta := by
      have hsmall := htd.trans_le (min_le_right T (eta / (L + 1)))
      nlinarith [(lt_div_iff₀ hL1).mp hsmall]

end PoincareConjecture.M44
