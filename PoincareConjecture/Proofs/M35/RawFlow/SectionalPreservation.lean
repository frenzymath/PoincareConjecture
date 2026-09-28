import PoincareConjecture.Proofs.M35.RawFlow.SectionalTimeSupport
import PoincareConjecture.Proofs.M04.ShiBarrierMaximum










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

open M04


theorem raw_nonnegative_sectional_on_slab
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime) :
    ∀ t ∈ Icc 0 T, (G.flow.connection t).NonnegativeSectionalCurvature := by
  let X := StandardCapSpace × StandardSectionalPair
  let : CompactSpace StandardSectionalPair :=
    isCompact_iff_compactSpace.mp (isCompact_modelOrthonormalPairs 3)
  obtain ⟨K, hK, hRm⟩ := G.curvature_locally_bounded T hT.le hTlt
  have hnorm (t : ℝ) (ht : t ∈ Icc 0 T) (x : StandardCapSpace) :
      (G.flow.connection t).curvatureTensorNorm x ≤ K := (le_abs_self _).trans (hRm t ht x)
  obtain ⟨C, hC, hsupp⟩ := exists_complete_distance_square_supports P G hT.le hTlt
  let L := 11 * K
  have hL : 0 ≤ L := by positivity
  let A := C + L
  have hA : 0 ≤ A := add_nonneg hC hL
  let q := rawSectionalRayleigh G
  let μ : ℝ → X → ℝ := fun s z => rawDistanceSquare G (0 : StandardCapSpace) s z.1
  have hμ (s : ℝ) (z : X) : 0 < μ s z := by dsimp [μ, rawDistanceSquare]; positivity
  have hqcont : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ univ) :=
    (continuousOn_rawSectionalRayleigh G).mono
      (prod_mono (fun _ ht => ⟨ht.1, ht.2.trans_lt hTlt⟩) Subset.rfl)
  have hμcont : ContinuousOn (Function.uncurry μ) (Icc 0 T ×ˢ univ) := by
    have hc : Continuous (fun z : ℝ × X => (z.1, z.2.1)) :=
      continuous_fst.prodMk (continuous_fst.comp continuous_snd)
    have hm : MapsTo (fun z : ℝ × X => (z.1, z.2.1))
        (Icc 0 T ×ˢ univ) (Icc 0 T ×ˢ univ) := fun z hz => ⟨hz.1, mem_univ _⟩
    have hh := (continuousOn_rawDistanceSquare G hT hTlt (0 : StandardCapSpace)).comp
      hc.continuousOn hm
    exact hh
  have hbound (s : ℝ) (hs : s ∈ Icc 0 T) (z : X) : -K ≤ q s z :=
    (abs_le.mp ((rawSectionalRayleigh_abs_le G s z).trans (hnorm s hs z.1))).1
  have hecont : Continuous (fun z : ℝ × X => Real.exp (A * z.1)) := by fun_prop
  have hε (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : t ∈ Icc 0 T) (z : X) :
      0 ≤ q t z + ε * Real.exp (A * t) * μ t z := by
    obtain ⟨S, hS, hzS, hexhaust⟩ := exists_raw_distance_square_compact_exhaustion
      P G hT.le hTlt (0 : StandardCapSpace) z.1 (A := K / ε) (by positivity)
    let W : Set X := S ×ˢ univ
    have hW : IsCompact W := hS.prod isCompact_univ
    have hWint : interior W = interior S ×ˢ (univ : Set StandardSectionalPair) := by
      change interior (S ×ˢ (univ : Set StandardSectionalPair)) = _
      rw [interior_prod_eq, interior_univ]
    let w : ℝ → X → ℝ := fun s y => q s y + ε * Real.exp (A * s) * μ s y
    have hwinit (y : X) (_hy : y ∈ W) : 0 ≤ w 0 y :=
      add_nonneg (rawSectionalRayleigh_initial_nonneg G y)
        (mul_nonneg (by positivity) (hμ 0 y).le)
    have hwboundary (s : ℝ) (hs : s ∈ Icc 0 T) (y : X)
        (hy : y ∈ W \ interior W) : 0 ≤ w s y := by
      have hyS : y.1 ∉ interior S := by
        intro hi
        apply hy.2
        rw [hWint]
        exact ⟨hi, mem_univ _⟩
      have hm := hexhaust s hs y.1 hyS
      have he : 1 ≤ Real.exp (A * s) := Real.one_le_exp_iff.mpr (mul_nonneg hA hs.1)
      have hmul := mul_le_mul_of_nonneg_left hm hε.le
      rw [mul_div_cancel₀ K hε.ne'] at hmul
      have hmore : ε * μ s y ≤ ε * Real.exp (A * s) * μ s y :=
        mul_le_mul_of_nonneg_right (by nlinarith : ε ≤ ε * Real.exp (A * s)) (hμ s y).le
      have hlow := hbound s hs y
      change 0 ≤ q s y + ε * Real.exp (A * s) * μ s y
      change K ≤ ε * μ s y at hmul
      linarith
    have hwcont : ContinuousOn (Function.uncurry w) (Icc 0 T ×ˢ W) :=
      (hqcont.add ((continuous_const.mul hecont).continuousOn.mul hμcont)).mono
        (prod_mono Subset.rfl (subset_univ W))
    have hwtest (s : ℝ) (hs : s ∈ Ioc 0 T) (y : X) (hy : y ∈ interior W)
        (hmin : ∀ z ∈ W, w s y ≤ w s z) (hneg : w s y < 0) (δ : ℝ) (hδ : 0 < δ) :
        ∃ χ : ℝ → ℝ, ∃ v : ℝ, χ s = w s y ∧
          (∀ᶠ r in 𝓝[Icc 0 s] s, w r y ≤ χ r) ∧
          HasDerivWithinAt χ v (Icc 0 s) s ∧ -(-L) * w s y - δ ≤ v := by
      have hyS : y.1 ∈ interior S := by
        rw [hWint] at hy
        exact hy.1
      exact raw_sectional_barrier_time_support G
        (show s ∈ Ico 0 G.lifetime from ⟨hs.1.le, hs.2.trans_lt hTlt⟩) hε
        (hnorm s ⟨hs.1.le, hs.2⟩) y hyS (hsupp s ⟨hs.1.le, hs.2⟩ 0 y.1)
        (fun z hz => hmin z ⟨hz, mem_univ _⟩) hneg δ hδ
    exact compact_subset_min_velocity_nonnegative_of_upper_support hW hT w hwinit hwboundary
      hwcont hwtest t ht z ⟨hzS, mem_univ _⟩
  have hqnonneg (t : ℝ) (ht : t ∈ Icc 0 T) (z : X) : 0 ≤ q t z := by
    by_contra hbad
    have hneg : q t z < 0 := lt_of_not_ge hbad
    let b := Real.exp (A * t) * μ t z
    have hb : 0 < b := mul_pos (Real.exp_pos _) (hμ t z)
    have hh := hε (-q t z / (2 * b))
      (div_pos (neg_pos.mpr hneg) (mul_pos zero_lt_two hb)) t ht z
    have heq : (-q t z / (2 * b)) * Real.exp (A * t) * μ t z = -q t z / 2 := by
      rw [mul_assoc]
      change (-q t z / (2 * b)) * b = -q t z / 2
      field_simp [hb.ne']
    rw [heq] at hh
    linarith
  intro t ht x u v
  simpa only [zero_mul] using sectional_lower_of_modelPairs (G.flow.connection t) x 0
    (fun p hp => hqnonneg t ht (x, ⟨p, hp⟩)) u v



theorem raw_nonnegative_sectional
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {t : ℝ} (ht : t ∈ Ico 0 G.lifetime) :
    (G.flow.connection t).NonnegativeSectionalCurvature := by
  let T := (t + G.lifetime) / 2
  have hT : 0 < T := by dsimp only [T]; linarith [G.lifetime_pos, ht.1]
  have hTlt : T < G.lifetime := by dsimp only [T]; linarith [ht.2]
  exact raw_nonnegative_sectional_on_slab P G hT hTlt t
    ⟨ht.1, by dsimp only [T]; linarith [ht.2]⟩

end PoincareConjecture.M35.Uniqueness
