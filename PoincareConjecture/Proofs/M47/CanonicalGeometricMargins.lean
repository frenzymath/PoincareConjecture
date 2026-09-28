import PoincareConjecture.Proofs.M47.CanonicalScalarStability
import PoincareConjecture.Proofs.M47.CanonicalMetricStability
import PoincareConjecture.Proofs.M34.Standard.CapIntrinsicDiameter










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem scalarCurvatureSupOn_eq_closure [CompactSpace M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hD : Continuous D.scalarCurvature) (A : Set M) :
    scalarCurvatureSupOn g D A = scalarCurvatureSupOn g D (closure A) := by
  classical
  by_cases hA : A.Nonempty
  · have hsubset : D.scalarCurvature '' A ⊆ D.scalarCurvature '' closure A :=
      image_mono subset_closure
    have hb : BddAbove (D.scalarCurvature '' closure A) :=
      isClosed_closure.isCompact.bddAbove_image hD.continuousOn
    have hlub := (isLUB_iff_of_subset_of_subset_closure hsubset
      (image_closure_subset_closure_image hD)).mp (isLUB_csSup (hA.image _) (hb.mono hsubset))
    have heq := hlub.csSup_eq ((hA.mono subset_closure).image D.scalarCurvature)
    simpa only [scalarCurvatureSupOn, ← image_eq_range] using heq.symm
  · have hAempty : A = ∅ := not_nonempty_iff_eq_empty.mp hA
    simp only [hAempty, closure_empty]



theorem continuous_scalarSup_on_set [CompactSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow 3 M J)
    (A : Set M) :
    Continuous (fun t : J => scalarCurvatureSupOn (F.metric t.val) (F.connection t.val) A) := by
  have hsame (t : J) : scalarCurvatureSupOn (F.metric t.val) (F.connection t.val) A =
      scalarCurvatureSupOn (F.metric t.val) (F.connection t.val) (closure A) := by
    have hD : Continuous (F.connection t.val).scalarCurvature := by
      have h := (hC.scalar_regular 3 M J F).continuousOn.comp_continuous
        (continuous_const.prodMk continuous_id : Continuous (fun x : M => (t.val, x)))
        (fun x => ⟨t.property, mem_univ x⟩)
      exact h
    exact scalarCurvatureSupOn_eq_closure _ _ hD A
  exact (continuous_scalarSup_on_compact hC F isClosed_closure.isCompact).congr
    (fun t => (hsame t).symm)

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

private theorem cap_scalarSup_pos {g : RiemannianMetric 3 M} (N : CapCertificate g) :
    0 < scalarCurvatureSupOn g N.connection N.carrier := by
  obtain ⟨x, hx⟩ := N.core_nonempty
  have hxcarrier : x ∈ N.carrier := by
    rw [N.core_eq_interior_closed_core] at hx
    have hclosed := interior_subset hx
    rw [N.closed_core_eq_complement_end] at hclosed
    exact hclosed.1
  obtain ⟨b, _, hratio⟩ := N.scalar_ratio
  have hb : BddAbove (range (fun y : N.carrier => N.connection.scalarCurvature y.val)) := by
    refine ⟨b * N.connection.scalarCurvature x, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hratio x hxcarrier y.val y.property
  exact (N.scalar_pos x hxcarrier).trans_le (le_csSup hb ⟨⟨x, hxcarrier⟩, rfl⟩)



theorem cap_intrinsic_diameter_bound_persists [CompactSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    (t : Icc a b) (N : CapCertificate (F.metric t.val))
    (hconnection : N.connection = F.connection t.val) :
    ∀ᶠ s : Icc a b in 𝓝 t,
      intrinsicDiameter (F.metric s.val) N.carrier <
        ENNReal.ofReal (N.cap_constant *
          scalarCurvatureSupOn (F.metric s.val) (F.connection s.val)
            N.carrier ^ (-1 / 2 : ℝ)) := by
  let S := fun s : Icc a b =>
    scalarCurvatureSupOn (F.metric s.val) (F.connection s.val) N.carrier
  let D := intrinsicDiameter (F.metric t.val) N.carrier
  have hS : Continuous S := continuous_scalarSup_on_set hC F N.carrier
  have hSpos : 0 < S t := by
    simpa only [S, ← hconnection] using cap_scalarSup_pos N
  have hold : D < ENNReal.ofReal (N.cap_constant * S t ^ (-1 / 2 : ℝ)) := by
    simpa only [D, S, ← hconnection] using N.intrinsic_diameter_bound
  have hDfinite : D ≠ ⊤ := ne_of_lt (hold.trans_le le_top)
  have hboundpos : 0 < N.cap_constant * S t ^ (-1 / 2 : ℝ) :=
    mul_pos N.cap_constant_pos (Real.rpow_pos_of_pos hSpos _)
  have holdreal : D.toReal < N.cap_constant * S t ^ (-1 / 2 : ℝ) := by
    have h := (ENNReal.toReal_lt_toReal hDfinite ENNReal.ofReal_ne_top).mpr hold
    simpa only [ENNReal.toReal_ofReal hboundpos.le] using h
  obtain ⟨K, _, hcompare⟩ := exists_compact_slab_metric_volume_comparison F
  let E := fun s : Icc a b => Real.exp (K * |s.val - t.val|)
  have hE : Continuous E :=
    Real.continuous_exp.comp
      (continuous_const.mul ((continuous_subtype_val.sub continuous_const).abs))
  have hright : ContinuousAt (fun s : Icc a b => N.cap_constant * S s ^ (-1 / 2 : ℝ)) t :=
    continuousAt_const.mul (hS.continuousAt.rpow_const (Or.inl hSpos.ne'))
  have hmargin : ∀ᶠ s : Icc a b in 𝓝 t,
      E s * D.toReal < N.cap_constant * S s ^ (-1 / 2 : ℝ) :=
    (hE.continuousAt.mul continuousAt_const).eventually_lt hright (by
      change E t * D.toReal < N.cap_constant * S t ^ (-1 / 2 : ℝ)
      simpa only [E, sub_self, abs_zero, mul_zero, Real.exp_zero, one_mul] using holdreal)
  filter_upwards [hmargin] with s hs
  have hnorm := (hcompare t.val t.property s.val s.property).1
  have hdiam := (F.metric t.val).intrinsicDiameter_image_le_mul (F.metric s.val)
    id N.carrier (fun _ _ => contMDiffAt_id) (Real.exp_pos (K * |s.val - t.val|))
    (fun x _ v => by
      simpa only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply] using hnorm x v)
  simp only [image_id] at hdiam
  apply hdiam.trans_lt
  have hpositive : 0 < N.cap_constant * S s ^ (-1 / 2 : ℝ) :=
    (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg).trans_lt hs
  have hof := (ENNReal.ofReal_lt_ofReal_iff hpositive).mpr hs
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_toReal hDfinite] at hof
  exact hof



theorem cap_volume_bound_persists [CompactSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) {a b : ℝ} (F : RicciFlow 3 M (Icc a b))
    (t : Icc a b) (N : CapCertificate (F.metric t.val))
    (hconnection : N.connection = F.connection t.val) :
    ∀ᶠ s : Icc a b in 𝓝 t,
      calibratedMetricVolume (F.metric s.val) N.carrier <
        ENNReal.ofReal N.cap_constant *
          ENNReal.ofReal (scalarCurvatureSupOn (F.metric s.val) (F.connection s.val)
            N.carrier ^ (-3 / 2 : ℝ)) := by
  let S := fun s : Icc a b =>
    scalarCurvatureSupOn (F.metric s.val) (F.connection s.val) N.carrier
  let V := calibratedMetricVolume (F.metric t.val) N.carrier
  have hS : Continuous S := continuous_scalarSup_on_set hC F N.carrier
  have hSpos : 0 < S t := by
    simpa only [S, ← hconnection] using cap_scalarSup_pos N
  have hold : V < ENNReal.ofReal (N.cap_constant * S t ^ (-3 / 2 : ℝ)) := by
    simpa only [V, S, ← hconnection, ENNReal.ofReal_mul N.cap_constant_pos.le]
      using N.volume_bound
  have hVfinite : V ≠ ⊤ := ne_of_lt (hold.trans_le le_top)
  have hboundpos : 0 < N.cap_constant * S t ^ (-3 / 2 : ℝ) :=
    mul_pos N.cap_constant_pos (Real.rpow_pos_of_pos hSpos _)
  have holdreal : V.toReal < N.cap_constant * S t ^ (-3 / 2 : ℝ) := by
    have h := (ENNReal.toReal_lt_toReal hVfinite ENNReal.ofReal_ne_top).mpr hold
    simpa only [ENNReal.toReal_ofReal hboundpos.le] using h
  obtain ⟨K, _, hcompare⟩ := exists_compact_slab_metric_volume_comparison F
  let E := fun s : Icc a b => Real.exp (K * |s.val - t.val|)
  have hE : Continuous E :=
    Real.continuous_exp.comp
      (continuous_const.mul ((continuous_subtype_val.sub continuous_const).abs))
  have hright : ContinuousAt (fun s : Icc a b => N.cap_constant * S s ^ (-3 / 2 : ℝ)) t :=
    continuousAt_const.mul (hS.continuousAt.rpow_const (Or.inl hSpos.ne'))
  have hmargin : ∀ᶠ s : Icc a b in 𝓝 t,
      E s ^ 3 * V.toReal < N.cap_constant * S s ^ (-3 / 2 : ℝ) :=
    ((hE.pow 3).continuousAt.mul continuousAt_const).eventually_lt hright (by
      change E t ^ 3 * V.toReal < N.cap_constant * S t ^ (-3 / 2 : ℝ)
      simpa only [E, sub_self, abs_zero, mul_zero, Real.exp_zero, one_pow, one_mul] using holdreal)
  filter_upwards [hmargin] with s hs
  apply ((hcompare t.val t.property s.val s.property).2.2 N.carrier).trans_lt
  have hpositive : 0 < N.cap_constant * S s ^ (-3 / 2 : ℝ) :=
    (mul_nonneg (pow_nonneg (Real.exp_pos _).le 3) ENNReal.toReal_nonneg).trans_lt hs
  have hof := (ENNReal.ofReal_lt_ofReal_iff hpositive).mpr hs
  rw [ENNReal.ofReal_mul (pow_nonneg (Real.exp_pos _).le 3),
    ENNReal.ofReal_pow (Real.exp_pos _).le, ENNReal.ofReal_toReal hVfinite,
    ENNReal.ofReal_mul N.cap_constant_pos.le] at hof
  exact hof

end PoincareConjecture.Proofs.M47
