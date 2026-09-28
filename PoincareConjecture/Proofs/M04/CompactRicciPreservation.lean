import PoincareConjecture.Proofs.M04.CompactTangentDirections
import PoincareConjecture.Proofs.M04.RicciRayleigh
import PoincareConjecture.Proofs.M04.RicciMinimumDiffusion
import PoincareConjecture.Proofs.M04.RicciNullReaction
import PoincareConjecture.Proofs.M04.CompactParabolic
import PoincareConjecture.Proofs.M04.ScalarEvolution
import Mathlib.Topology.Homeomorph.Lemmas








set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology

universe u

namespace PoincareConjecture.M04

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

set_option maxHeartbeats 4800000 in

set_option backward.isDefEq.respectTransparency false in
theorem nonnegativeRicciCurvature_preserved_compact
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {T : ℝ} (hT : 0 < T) (F : RicciFlow 3 M (Icc 0 T))
    (hinit : (F.connection 0).NonnegativeRicciCurvature) :
    ∀ t ∈ Icc 0 T, (F.connection t).NonnegativeRicciCurvature := by
  classical
  let E := EuclideanSpace ℝ (Fin 3)
  let e := fun c : M ↦ trivializationAt E (TangentSpace (𝓡 3) : M → Type _) c
  obtain ⟨s, K, hK, hKe, hcover⟩ := exists_finite_compact_tangent_cover (n := 3) (M := M)
  let Sphere := Metric.sphere (0 : E) 1
  let C := (i : s) × (K i.1) × Sphere
  let (c : M) : CompactSpace (K c) := isCompact_iff_compactSpace.mp (hK c)
  let : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E) 1)
  let : CompactSpace C := inferInstance
  let X : C → M := fun z ↦ z.2.1.1
  let V : (z : C) → TangentSpace (𝓡 3) (X z) :=
    fun z ↦ (e z.1.1).symmL ℝ (X z) z.2.2.1
  have hsphere {w : E} (hw : w ∈ Sphere) : w ≠ 0 := by
    intro hw0
    simp [Sphere, Metric.mem_sphere, hw0] at hw
  have hV (z : C) : V z ≠ 0 := by
    intro hz
    have hw := congrArg ((e z.1.1).continuousLinearMapAt ℝ (X z)) hz
    have he : z.2.2.1 = 0 := by
      have hy : X z ∈ (e z.1.1).baseSet := hKe z.1.1 z.2.1.2
      change (e z.1.1).continuousLinearMapAt ℝ (X z)
        ((e z.1.1).symmL ℝ (X z) z.2.2.1) =
          (e z.1.1).continuousLinearMapAt ℝ (X z) 0 at hw
      rw [(e z.1.1).continuousLinearMapAt_symmL hy, map_zero] at hw
      exact hw
    exact hsphere z.2.2.2 he
  let R : ℝ → C → ℝ := fun t z ↦ (F.connection t).ricci (X z) (V z) (V z)
  let G : ℝ → C → ℝ := fun t z ↦ (F.metric t).inner (X z) (V z) (V z)
  let q : ℝ → C → ℝ := fun t z ↦ R t z / G t z
  have hG (t : ℝ) (z : C) : 0 < G t z := (F.metric t).pos (X z) (V z) (hV z)
  have hX : Continuous X := by
    apply continuous_sigma
    intro i
    exact continuous_subtype_val.comp continuous_fst
  have hqc : Continuous (fun p : (Icc (0 : ℝ) T) × C ↦ q p.1 p.2) := by
    let D := (i : s) × ((K i.1) × Sphere) × Icc (0 : ℝ) T
    let d : C × Icc (0 : ℝ) T ≃ₜ D := Homeomorph.sigmaProdDistrib
    have h : Continuous (fun z : D ↦ q z.2.2 ⟨z.1, z.2.1⟩) := by
      apply continuous_sigma
      intro i
      have hp : Continuous (fun p : ((K i.1) × Sphere) × Icc (0 : ℝ) T ↦
          (((p.2 : ℝ), (p.1.1 : M)), (p.1.2 : E))) := by fun_prop
      exact (continuousOn_flow_ricciRayleigh_trivialization F i.1).comp_continuous hp
        (fun p ↦ ⟨⟨p.2.2, hKe i.1 p.1.1.2⟩, hsphere p.1.2.2⟩)
    have hs : Continuous (fun p : C × Icc (0 : ℝ) T ↦ q p.2 p.1) :=
      h.comp d.continuous
    exact hs.comp continuous_swap
  have hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ (univ : Set C)) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hmap : Continuous (fun p : Icc 0 T ×ˢ (univ : Set C) ↦
        ((⟨p.1.1, p.2.1⟩ : Icc (0 : ℝ) T), p.1.2)) := by fun_prop
    exact hqc.comp hmap
  have hRicScale (t : ℝ) (y : M) (v : TangentSpace (𝓡 3) y) (r : ℝ) :
      (F.connection t).ricci y (r • v) (r • v) = r ^ 2 * (F.connection t).ricci y v v := by
    obtain ⟨A, hA⟩ := (isSmoothCovariantTensor_ricciEvaluation (F.connection t)).1 y
    have ha := A.map_smul_univ (fun _ ↦ r) ![v, v]
    have htup : (fun i : Fin 2 ↦ r • (![v, v] : Fin 2 → TangentSpace (𝓡 3) y) i) =
        ![r • v, r • v] := by funext i; fin_cases i <;> rfl
    simpa only [htup, ← hA, LeviCivitaData.ricciEvaluation, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, smul_eq_mul, pow_two]
      using ha
  have hMetricScale (t : ℝ) (y : M) (v : TangentSpace (𝓡 3) y) (r : ℝ) :
      (F.metric t).inner y (r • v) (r • v) = r ^ 2 * (F.metric t).inner y v v := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hcomplete (t m : ℝ) (h : ∀ z : C, m ≤ q t z) :
      ∀ (y : M) (v : TangentSpace (𝓡 3) y),
        m * (F.metric t).inner y v v ≤ (F.connection t).ricci y v v := by
    intro y u
    by_cases hu : u = 0
    · subst u
      have hzero : (F.connection t).ricci y 0 0 = 0 := by
        simpa only [zero_smul, zero_pow (by decide : 2 ≠ 0), zero_mul]
          using hRicScale t y 0 0
      rw [hzero]
      have hgzero : (F.metric t).inner y 0 0 = 0 := by simp
      rw [hgzero, mul_zero]
    have hycover : y ∈ ⋃ c ∈ s, K c := hcover ▸ mem_univ y
    obtain ⟨c, hc, hyK⟩ := mem_iUnion₂.mp hycover
    have hy : y ∈ (e c).baseSet := hKe c hyK
    let a := (e c).continuousLinearMapAt ℝ y u
    have ha : a ≠ 0 := by
      intro ha0
      have hz := congrArg ((e c).symmL ℝ y) ha0
      apply hu
      simpa only [a, (e c).symmL_continuousLinearMapAt hy, map_zero] using hz
    let r := ‖a‖
    have hr : 0 < r := norm_pos_iff.mpr ha
    let w := r⁻¹ • a
    have hw : w ∈ Sphere := by
      change dist w 0 = 1
      rw [dist_zero_right]
      exact norm_smul_inv_norm ha
    let z : C := ⟨⟨c, hc⟩, ⟨⟨y, hyK⟩, ⟨w, hw⟩⟩⟩
    have hzV : V z = r⁻¹ • u := by
      change (e c).symmL ℝ y (r⁻¹ • a) = _
      rw [map_smul, (e c).symmL_continuousLinearMapAt hy]
    have huV : u = r • V z := by
      rw [hzV, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hi : m * (F.metric t).inner y (V z) (V z) ≤
        (F.connection t).ricci y (V z) (V z) := (le_div_iff₀ (hG t z)).mp (h z)
    have hmetric : (F.metric t).inner y u u =
        r ^ 2 * (F.metric t).inner y (V z) (V z) :=
      (congrArg (fun w ↦ (F.metric t).inner y w w) huV).trans (hMetricScale t y (V z) r)
    have hricci : (F.connection t).ricci y u u =
        r ^ 2 * (F.connection t).ricci y (V z) (V z) :=
      (congrArg (fun w ↦ (F.connection t).ricci y w w) huV).trans (hRicScale t y (V z) r)
    calc
      m * (F.metric t).inner y u u =
          r ^ 2 * (m * (F.metric t).inner y (V z) (V z)) := by
            rw [hmetric]
            ring
      _ ≤ r ^ 2 * (F.connection t).ricci y (V z) (V z) :=
        mul_le_mul_of_nonneg_left hi (sq_nonneg r)
      _ = (F.connection t).ricci y u u := hricci.symm
  have hscalar : Continuous (fun p : (Icc (0 : ℝ) T) × C ↦
      (F.connection p.1).scalarCurvature (X p.2)) :=
    F.contMDiffOn_scalarCurvature.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk (hX.comp continuous_snd))
      (fun p ↦ ⟨p.1.2, mem_univ (X p.2)⟩)
  obtain ⟨A, hA⟩ := isCompact_univ.bddAbove_image (hscalar.sub hqc).continuousOn
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) (z : C) :
      (F.connection t).scalarCurvature (X z) - q t z ≤ A :=
    hA ⟨(⟨t, ht⟩, z), mem_univ _, rfl⟩
  let L : ℝ → C → ℝ := fun t z ↦
    (F.connection t).tensorLaplacian (F.connection t).ricciEvaluation (X z) ![V z, V z]
  let Q : ℝ → C → ℝ := fun t z ↦ (F.connection t).ricciReaction (X z) (V z) (V z)
  let velocity : ℝ → C → ℝ := fun t z ↦ (L t z + Q t z) / G t z + 2 * (q t z) ^ 2
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) (z : C) :
      HasDerivWithinAt (fun s ↦ q s z) (velocity t z) (Icc 0 T) t :=
    hasDerivWithinAt_ricciRayleigh F t ht (X z) (V z) (hV z)
  have hminimum (t : ℝ) (ht : t ∈ Ioc 0 T) (z : C)
      (hspace : ∀ y : C, q t z ≤ q t y) (hnonpos : q t z ≤ 0) :
      -(-A) * q t z ≤ velocity t z := by
    let m := q t z
    have hlower := hcomplete t m hspace
    have hnull : (F.connection t).ricci (X z) (V z) (V z) =
        m * (F.metric t).inner (X z) (V z) (V z) := by
      exact (div_mul_cancel₀ (R t z) (hG t z).ne').symm
    have hlap : 0 ≤ L t z :=
      ricci_tensorLaplacian_nonneg_at_rayleigh_min (F.connection t) m hlower (X z) (V z) hnull
    have hshift : ∀ v : TangentSpace (𝓡 3) (X z),
        0 ≤ (F.connection t).ricci (X z) v v + (-m) * (F.metric t).inner (X z) v v := by
      intro v
      have h := hlower (X z) v
      linarith
    have hzshift : (F.connection t).ricci (X z) (V z) (V z) +
        (-m) * (F.metric t).inner (X z) (V z) (V z) = 0 := by rw [hnull]; ring
    have hreact : m * ((F.connection t).scalarCurvature (X z) - m) * G t z ≤
        Q t z + 2 * m * R t z := by
      have h := ricciReaction_lower_bound_of_shiftedRicci_null
        (F.connection t) (X z) (-m) hshift (V z) hzshift
      convert! h using 1 <;> ring
    have hvelocity : velocity t z * G t z = L t z + Q t z + 2 * m * R t z := by
      change ((L t z + Q t z) / G t z + 2 * m ^ 2) * G t z = _
      have hr : R t z = m * G t z := hnull
      rw [hr]
      field_simp [(hG t z).ne']
    have hreaction : m * ((F.connection t).scalarCurvature (X z) - m) ≤ velocity t z := by
      apply (mul_le_mul_iff_left₀ (hG t z)).mp
      nlinarith only [hreact, hlap, hvelocity]
    have hb := hbound t ⟨ht.1.le, ht.2⟩ z
    change (F.connection t).scalarCurvature (X z) - m ≤ A at hb
    change m ≤ 0 at hnonpos
    change -(-A) * m ≤ velocity t z
    simp only [neg_neg]
    nlinarith only [hreaction, hb, hnonpos]
  have hqinit (z : C) : 0 ≤ q 0 z := div_nonneg (hinit (X z) (V z)) (hG 0 z).le
  have hpres := compact_min_velocity_nonnegative (K := -A) hT q velocity hq hd hminimum hqinit
  intro t ht
  change ∀ (y : M) (v : TangentSpace (𝓡 3) y), 0 ≤ (F.connection t).ricci y v v
  simpa only [zero_mul] using hcomplete t 0 (hpres t ht)

end PoincareConjecture.M04

