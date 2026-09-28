import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.SectionalParameters
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.SectionalLocalDiffusion









set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.M04

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency false in


theorem clopen_sectional_lower_preserved
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {T c : ℝ} (hT : 0 < T) (hc : 0 ≤ c) (F : RicciFlow 3 M (Icc 0 T))
    {S : Set M} (hSopen : IsOpen S) (hSclosed : IsClosed S)
    (hinit : ∀ y ∈ S, ∀ a b : TangentSpace (𝓡 3) y,
      c * metricGram (F.metric 0) y a b ≤ (F.connection 0).curvatureTensor y a b a b) :
    ∀ t ∈ Icc 0 T, ∀ y ∈ S, ∀ a b : TangentSpace (𝓡 3) y,
      c * metricGram (F.metric t) y a b ≤ (F.connection t).curvatureTensor y a b a b := by
  obtain ⟨P⟩ := compactSectionalParameters F
  let C := P.point ⁻¹' S
  let : CompactSpace C :=
    isCompact_iff_compactSpace.mp (hSclosed.preimage P.point_continuous).isCompact
  let X : C → M := fun z => P.point z.1
  let U : (z : C) → TangentSpace (𝓡 3) (X z) := fun z => P.left z.1
  let V : (z : C) → TangentSpace (𝓡 3) (X z) := fun z => P.right z.1
  let R : ℝ → C → ℝ := fun t z =>
    (F.connection t).curvatureTensor (X z) (U z) (V z) (U z) (V z)
  let G : ℝ → C → ℝ := fun t z => metricGram (F.metric t) (X z) (U z) (V z)
  let q : ℝ → C → ℝ := fun t z => R t z / G t z
  have hG (t : ℝ) (z : C) : 0 < G t z :=
    metricGram_pos_of_linearIndependent (F.metric t) (X z) (U z) (V z) (P.independent z.1)
  have hmap : Continuous (fun p : ℝ × C => (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ (univ : Set C)) :=
    P.continuous_quotient.comp hmap.continuousOn (fun p hp => ⟨hp.1, mem_univ _⟩)
  have hcomplete (t m : ℝ) (h : ∀ z : C, m ≤ q t z) :
      ∀ y ∈ S, ∀ a b : TangentSpace (𝓡 3) y,
        m * metricGram (F.metric t) y a b ≤ (F.connection t).curvatureTensor y a b a b :=
    P.complete_on S t m (fun z hz =>
      (le_div_iff₀ (hG t ⟨z, hz⟩)).mp (h ⟨z, hz⟩))
  have hqi (z : C) : c ≤ q 0 z :=
    (le_div_iff₀ (hG 0 z)).mpr (hinit (X z) z.2 (U z) (V z))
  have hX : Continuous X := P.point_continuous.comp continuous_subtype_val
  have hqc : Continuous (fun p : (Icc (0 : ℝ) T) × C => q p.1 p.2) :=
    hq.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p => ⟨p.1.2, mem_univ _⟩)
  have hscalar : Continuous (fun p : (Icc (0 : ℝ) T) × C =>
      (F.connection p.1).scalarCurvature (X p.2)) :=
    F.contMDiffOn_scalarCurvature.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk (hX.comp continuous_snd))
      (fun p => ⟨p.1.2, mem_univ _⟩)
  obtain ⟨A0, hA0⟩ := isCompact_univ.bddAbove_image
    (hscalar.sub (continuous_const.mul hqc)).continuousOn
  let A := max 0 A0
  have hA : 0 ≤ A := le_max_left _ _
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) (z : C) :
      (F.connection t).scalarCurvature (X z) - 2 * q t z ≤ A :=
    (hA0 ⟨(⟨t, ht⟩, z), mem_univ _, rfl⟩).trans (le_max_right _ _)
  let L : ℝ → C → ℝ := fun t z =>
    (F.connection t).tensorLaplacian (F.connection t).riemannEvaluation
      (X z) ![U z, V z, U z, V z]
  let Q : ℝ → C → ℝ := fun t z =>
    (F.connection t).curvatureReaction (X z) (U z) (V z) (U z) (V z)
  let H : ℝ → C → ℝ := fun t z =>
    -2 * (F.connection t).ricci (X z) (U z) (U z) * (F.metric t).inner (X z) (V z) (V z) -
      2 * (F.metric t).inner (X z) (U z) (U z) * (F.connection t).ricci (X z) (V z) (V z) +
      4 * (F.connection t).ricci (X z) (U z) (V z) * (F.metric t).inner (X z) (U z) (V z)
  let velocity : ℝ → C → ℝ := fun t z =>
    (L t z + Q t z) / G t z - R t z * H t z / (G t z) ^ 2
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) (z : C) :
      HasDerivWithinAt (fun s => q s z) (velocity t z) (Icc 0 T) t :=
    hasDerivWithinAt_sectionalRayleigh F t ht (X z) (U z) (V z) (hG t z)
  have hminimum (t : ℝ) (ht : t ∈ Ioc 0 T) (z : C)
      (hspace : ∀ y : C, q t z ≤ q t y) (hbelow : q t z - c ≤ 0) :
      A * (q t z - c) ≤ velocity t z := by
    let m := q t z
    have hlower := hcomplete t m hspace
    have hnull : (F.connection t).curvatureTensor (X z) (U z) (V z) (U z) (V z) =
        m * metricGram (F.metric t) (X z) (U z) (V z) :=
      (div_mul_cancel₀ (R t z) (hG t z).ne').symm
    have hlap : 0 ≤ L t z :=
      sectional_laplacian_nonneg_of_local_lower (F.connection t)
        m hSopen hlower (X z) z.2 (U z) (V z) hnull
    have hshift : ∀ a b : TangentSpace (𝓡 3) (X z),
        0 ≤ (F.connection t).curvatureTensor (X z) a b a b +
          (-m) * metricGram (F.metric t) (X z) a b := by
      intro a b
      have h := hlower (X z) z.2 a b
      linarith
    have hzshift : (F.connection t).curvatureTensor (X z) (U z) (V z) (U z) (V z) +
        (-m) * metricGram (F.metric t) (X z) (U z) (V z) = 0 := by rw [hnull]; ring
    have hreact : m * ((F.connection t).scalarCurvature (X z) - 2 * m) * G t z ≤
        Q t z - m * H t z := by
      have h := curvatureReaction_lower_bound_of_shiftedSectional_null
        (F.connection t) (X z) (-m) hshift (U z) (V z) hzshift
      change -(-m) * ((F.connection t).scalarCurvature (X z) + 2 * (-m)) * G t z ≤
        Q t z + (-m) * H t z at h
      convert! h using 1 <;> ring
    have hvelocity : velocity t z * G t z = L t z + Q t z - m * H t z := by
      change ((L t z + Q t z) / G t z - R t z * H t z / (G t z) ^ 2) * G t z = _
      have hr : R t z = m * G t z := hnull
      rw [hr]
      field_simp [(hG t z).ne']
    have hreaction : m * ((F.connection t).scalarCurvature (X z) - 2 * m) ≤ velocity t z := by
      apply (mul_le_mul_iff_left₀ (hG t z)).mp
      nlinarith only [hreact, hlap, hvelocity]
    by_cases hm : 0 ≤ m
    · have hscalar := scalar_lower_of_sectional_lower (F.connection t) (X z) m
        (hlower (X z) z.2)
      have hscalar' : 0 ≤ (F.connection t).scalarCurvature (X z) - 2 * m := by linarith
      exact (mul_nonpos_of_nonneg_of_nonpos hA hbelow).trans
        ((mul_nonneg hm hscalar').trans hreaction)
    · have hb := hbound t ⟨ht.1.le, ht.2⟩ z
      have hmul := mul_le_mul_of_nonpos_left hb (le_of_not_ge hm)
      have hcA := mul_nonneg hA hc
      change A * (m - c) ≤ velocity t z
      nlinarith only [hmul, hcA, hreaction]
  have hpres := compact_min_velocity_nonnegative (K := -A) hT
    (fun t z => q t z - c) velocity (hq.sub continuousOn_const)
    (fun t ht z => (hd t ht z).sub_const c)
    (fun t ht z hmin hbelow => by
      have hm : ∀ y : C, q t z ≤ q t y := by
        intro y
        have h := hmin y
        linarith
      simpa only [neg_neg] using hminimum t ht z hm hbelow)
    (fun z => sub_nonneg.mpr (hqi z))
  intro t ht
  exact hcomplete t c (fun z => sub_nonneg.mp (hpres t ht z))



theorem compact_sectional_lower_preserved
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {T c : ℝ} (hT : 0 < T) (hc : 0 ≤ c) (F : RicciFlow 3 M (Icc 0 T))
    (hinit : ∀ y : M, ∀ a b : TangentSpace (𝓡 3) y,
      c * metricGram (F.metric 0) y a b ≤ (F.connection 0).curvatureTensor y a b a b) :
    ∀ t ∈ Icc 0 T, ∀ y : M, ∀ a b : TangentSpace (𝓡 3) y,
      c * metricGram (F.metric t) y a b ≤ (F.connection t).curvatureTensor y a b a b := by
  intro t ht y a b
  exact clopen_sectional_lower_preserved hT hc F isOpen_univ isClosed_univ
    (fun z _ => hinit z) t ht y (mem_univ _) a b

end PoincareConjecture.Proofs.M46
