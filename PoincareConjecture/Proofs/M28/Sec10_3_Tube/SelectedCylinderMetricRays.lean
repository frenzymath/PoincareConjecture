import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedCylinderCompletion
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.FixedWallIntrinsicSegments
import PoincareConjecture.Proofs.M28.Mathlib.CompactPrefixRay

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} {X : Set M}

theorem exists_selected_cylinder_metric_rays
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) = A.tail true (1 / 2))
    (hA : SmoothSphereIsotopicIn T.carrier A.middleSphere T.cylinder.middleSphere)
    (D : LeviCivitaData g) (hR : ContinuousOn D.scalarCurvature T.carrier)
    (hratio : ∀ i ∈ T.chain.shape.active,
      ∀ y ∈ (T.chain.neck i).carrier, ∀ z ∈ (T.chain.neck i).carrier,
        D.scalarCurvature y ≤ 2 * D.scalarCurvature z)
    (hdiverge : ∀ B : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ x ∈ T.carrier, d < (A.inverse x).2 → B < D.scalarCurvature x)
    {B : ℝ} (hB : 0 < B) (hdiam : intrinsicDiameter g (U : Set M) ≤ ENNReal.ofReal B)
    (hsmall : T.epsilon ≤ neckShorteningEpsilon)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    letI := intrinsicOpenMetricSpace g U hfinite
    ∃ E : UniformSpace.Completion U,
      let r : U → ℝ := fun x => dist (x : UniformSpace.Completion U) E
      E ∉ Set.range ((↑) : U → UniformSpace.Completion U) ∧
      Continuous r ∧ (∀ x : U, 0 < r x) ∧
      (∀ x y : U, |r x - r y| ≤ dist x y ∧ dist x y ≤ r x + r y) ∧
      (∀ eta : ℝ, 0 < eta → ∃ c : ℝ, 1 / 2 < c ∧ c < 1 ∧
        ∀ x : U, c < (A.inverse x).2 → r x < eta) ∧
      (∀ q : ℕ → U, Tendsto (fun n => (A.inverse (q n)).2) atTop (𝓝 1) →
        Tendsto (fun n => (q n : UniformSpace.Completion U)) atTop (𝓝 E)) ∧
      ∃ i ∈ T.chain.shape.active, ∃ (f : M → ℝ) (b : ℝ), 1 / 2 < b ∧ b < 1 ∧
        ContinuousOn f T.carrier ∧
        (∀ x ∈ T.carrier, f x = 0 ↔ x ∈ (T.chain.neck i).central_sphere) ∧
        (T.chain.neck i).carrier ⊆ (U : Set M) ∧
        (∀ x ∈ T.carrier, b < (A.inverse x).2 → 0 < f x) ∧
        (∀ p q : U, 0 < f p → 0 < f q →
          ∃ mu : ℝ → U, mu 0 = p ∧ mu 1 = q ∧ Continuous mu ∧
            (∀ t : ℝ, (3 / 4 : ℝ) ≤ (A.inverse (mu t)).2) ∧
            ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
              (intrinsicOpenMetric g U).edist (mu s) (mu t) =
                ENNReal.ofReal |s - t| * (intrinsicOpenMetric g U).edist p q) ∧
        ∀ p : U, 0 < f p → ∃ gamma : ℝ → U,
          gamma 0 = p ∧ Isometry (fun t : Ico (0 : ℝ) (r p) => gamma t.1) ∧
          (∀ s ∈ Ico (0 : ℝ) (r p), ∀ t ∈ Ico (0 : ℝ) (r p),
            dist (gamma s) (gamma t) = |s - t|) ∧
          (∀ t ∈ Ico (0 : ℝ) (r p), r (gamma t) = r p - t) ∧
          ∀ t ∈ Ico (0 : ℝ) (r p), (3 / 4 : ℝ) ≤ (A.inverse (gamma t)).2 := by
  classical
  let := intrinsicOpenMetricSpace g U hfinite
  let gU := intrinsicOpenMetric g U
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨gU.toRiemannianMetric⟩
  have hed (x y : U) : gU.edist x y = ENNReal.ofReal (dist x y) := by
    change edist x y = _
    exact edist_dist x y
  have hUV : (U : Set M) ⊆ T.carrier := by
    rw [hU]
    exact A.tail_subset_m28 true (by norm_num) (by norm_num)
  have hheight : Continuous (fun x : U => (A.inverse x).2) :=
    continuousOn_iff_continuous_domRestrict.mp
      ((continuous_snd.comp_continuousOn A.inverse_smooth.continuousOn).mono hUV)
  have hbelow (x : U) : (A.inverse x).2 < 1 :=
    (A.inverse_mem x (hUV x.property)).2.2
  obtain ⟨E, ⟨houtside, htail, hsequences, hcontinuous, hpositive, htriangle⟩, _hunique⟩ :=
    exists_unique_selected_cylinder_completion T A U hU hA D hR hratio hdiverge hB hdiam hfinite
  let r : U → ℝ := fun x => dist (x : UniformSpace.Completion U) E
  obtain ⟨i, hi, f, b, hbhalf, hb1, hf, hzero, hNU, hhigh, hsegments⟩ :=
    exists_fixed_wall_intrinsic_segments T A U hU hA D.scalarCurvature hR hratio
      hdiverge hsmall hfinite
  refine ⟨E, houtside, hcontinuous, hpositive, htriangle, htail, hsequences,
    i, hi, f, b, hbhalf, hb1, hf, hzero, hNU, hhigh, hsegments, ?_⟩
  intro p hp
  let a : ℝ := r p
  have ha : 0 < a := hpositive p
  have hpoint (n : ℕ) : ∃ q : U, b < (A.inverse q).2 ∧
      (A.inverse p).2 < (A.inverse q).2 ∧
      1 - 1 / ((n : ℝ) + 1) < (A.inverse q).2 := by
    let c : ℝ := max (max b (A.inverse p).2) (1 - 1 / ((n : ℝ) + 1))
    have hlevel : 1 - 1 / ((n : ℝ) + 1) < 1 := by
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hcpos : 0 < c :=
      lt_max_of_lt_left (lt_max_of_lt_left (lt_trans (by norm_num) hbhalf))
    have hc1 : c < 1 := max_lt (max_lt hb1 (hbelow p)) hlevel
    obtain ⟨q, hq⟩ := A.tail_nonempty true hcpos hc1
    have hqread := (A.mem_tail_iff_m28 true hcpos hc1).mp hq
    have hcb : b ≤ c := (le_max_left _ _).trans (le_max_left _ _)
    have hcp : (A.inverse p).2 ≤ c := (le_max_right _ _).trans (le_max_left _ _)
    have hcl : 1 - 1 / ((n : ℝ) + 1) ≤ c := le_max_right _ _
    have hqU : q ∈ (U : Set M) := by
      rw [hU]
      exact (A.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr
        ⟨hqread.1, hbhalf.trans (hcb.trans_lt hqread.2)⟩
    exact ⟨⟨q, hqU⟩, hcb.trans_lt hqread.2, hcp.trans_lt hqread.2,
      hcl.trans_lt hqread.2⟩
  choose q hqb hqp hqlevel using hpoint
  have hlevels : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hqheight : Tendsto (fun n => (A.inverse (q n)).2) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hlevels tendsto_const_nhds
      (fun n => (hqlevel n).le) (fun n => (hbelow (q n)).le)
  have hqE := hsequences q hqheight
  let length (n : ℕ) : ℝ := dist p (q n)
  have hlengthPos (n : ℕ) : 0 < length n := by
    apply dist_pos.mpr
    intro hpq
    have h := hqp n
    rw [← hpq] at h
    exact (lt_irrefl _) h
  have hlength : Tendsto length atTop (𝓝 a) := by
    change Tendsto (fun n => dist p (q n)) atTop
      (𝓝 (dist (p : UniformSpace.Completion U) E))
    simpa only [UniformSpace.Completion.dist_eq] using
      (tendsto_const_nhds (x := (p : UniformSpace.Completion U))).dist hqE
  have hdefect : Tendsto (fun n => r (q n)) atTop (𝓝 0) := by
    change Tendsto (fun n => dist (q n : UniformSpace.Completion U) E) atTop (𝓝 0)
    simpa only [dist_self] using hqE.dist (tendsto_const_nhds (x := E))
  choose mu hmu0 hmu1 _hmuContinuous hmuLower hmuMetric using fun n =>
    hsegments p (q n) hp (hhigh (q n) (hUV (q n).property) (hqb n))
  have hunit (n : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      dist (mu n s) (mu n t) = |s - t| * length n := by
    have h := hmuMetric n s hs t ht
    rw [hed, hed, ← ENNReal.ofReal_mul (abs_nonneg (s - t))] at h
    exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg
      (mul_nonneg (abs_nonneg _) (hlengthPos n).le)).mp h
  let arc (n : ℕ) (t : ℝ) : U := mu n (t / length n)
  have hanchor (n : ℕ) : arc n 0 = p := by
    simpa only [arc, zero_div] using hmu0 n
  have hendpoint (n : ℕ) : arc n (length n) = q n := by
    simpa only [arc, div_self (hlengthPos n).ne'] using hmu1 n
  have hparameter (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (length n)) :
      t / length n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht.1 (hlengthPos n).le, (div_le_one (hlengthPos n)).mpr ht.2⟩
  have harcMetric (n : ℕ) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (length n))
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (length n)) :
      dist (arc n s) (arc n t) = |s - t| := by
    change dist (mu n (s / length n)) (mu n (t / length n)) = _
    rw [hunit n _ (hparameter n s hs) _ (hparameter n t ht),
      ← sub_div, abs_div, abs_of_pos (hlengthPos n),
      div_mul_cancel₀ _ (hlengthPos n).ne']
  have harcLower (n : ℕ) (t : ℝ) : (3 / 4 : ℝ) ≤ (A.inverse (arc n t)).2 :=
    hmuLower n (t / length n)
  have hradiusBounds (n : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (length n)) :
      a - t ≤ r (arc n t) ∧ r (arc n t) ≤ length n - t + r (q n) := by
    have hstart := harcMetric n 0 ⟨le_rfl, (hlengthPos n).le⟩ t ht
    rw [hanchor n] at hstart
    have hstart' : dist p (arc n t) = t := by
      simpa only [zero_sub, abs_neg, abs_of_nonneg ht.1] using hstart
    have hend := harcMetric n t ht (length n) ⟨(hlengthPos n).le, le_rfl⟩
    rw [hendpoint n] at hend
    have hend' : dist (arc n t) (q n) = length n - t := by
      simpa only [abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub] using hend
    have hlow := (le_abs_self (r p - r (arc n t))).trans (htriangle p (arc n t)).1
    have hupp := (le_abs_self (r (arc n t) - r (q n))).trans
      (htriangle (arc n t) (q n)).1
    rw [hstart'] at hlow
    rw [hend'] at hupp
    change r p - t ≤ r (arc n t) ∧ r (arc n t) ≤ length n - t + r (q n)
    constructor <;> linarith
  have hprefix : ∀ T0 : ℝ, 0 < T0 → T0 < a →
      ∃ K : Set U, IsCompact K ∧
        ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T0, arc n t ∈ K := by
    intro T0 _hT0 hT0a
    obtain ⟨d, _hdhalf, hd1, hdecay⟩ := htail ((a - T0) / 2)
      (half_pos (sub_pos.mpr hT0a))
    let upper : ℝ := max d (3 / 4 : ℝ)
    have hupper : upper < 1 := max_lt hd1 (by norm_num)
    have hKambient : IsCompact (A.compactSlab (3 / 4) upper) :=
      A.isCompact_compactSlab (by norm_num) hupper
    have hKU : A.compactSlab (3 / 4) upper ⊆ (U : Set M) := by
      intro x hx
      have hxread := (A.mem_compactSlab_iff (by norm_num) hupper).mp hx
      rw [hU]
      exact (A.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr
        ⟨hxread.1, (by norm_num : (1 / 2 : ℝ) < 3 / 4).trans_le hxread.2.1⟩
    let K : Set U := (Subtype.val : U → M) ⁻¹' A.compactSlab (3 / 4) upper
    have hK : IsCompact K :=
      Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hKambient
        (fun x hx => ⟨⟨x, hKU hx⟩, rfl⟩)
    refine ⟨K, hK, ?_⟩
    filter_upwards [hlength.eventually (lt_mem_nhds hT0a)] with n hn
    intro t ht
    have hbound := (hradiusBounds n t ⟨ht.1, ht.2.trans hn.le⟩).1
    have hheightUpper : (A.inverse (arc n t)).2 ≤ d := by
      apply le_of_not_gt
      intro hhighArc
      have hsmallArc := hdecay (arc n t) hhighArc
      change r (arc n t) < (a - T0) / 2 at hsmallArc
      linarith [ht.2]
    change (arc n t : M) ∈ A.compactSlab (3 / 4) upper
    exact (A.mem_compactSlab_iff (by norm_num) hupper).mpr
      ⟨hUV (arc n t).property, harcLower n t, hheightUpper.trans (le_max_left _ _)⟩
  obtain ⟨gamma, hgamma0, hgammaIsometry, hgammaMetric, hgammaLimit⟩ :=
    exists_isometric_finite_ray_of_compact_prefixes ha hlength
      (Eventually.of_forall hanchor) hprefix harcMetric
  have hgammaRadius : ∀ t ∈ Ico (0 : ℝ) a, r (gamma t) = a - t := by
    apply finite_ray_radius_eq_of_source_bounds (r := r) hcontinuous hlength hdefect hgammaLimit
    intro t ht
    exact (hlength.eventually (lt_mem_nhds ht.2)).mono fun n hn =>
      hradiusBounds n t ⟨ht.1, hn.le⟩
  refine ⟨gamma, hgamma0, hgammaIsometry, hgammaMetric, hgammaRadius, ?_⟩
  intro t ht
  apply ge_of_tendsto ((hheight.tendsto (gamma t)).comp (hgammaLimit t ht))
  exact Eventually.of_forall fun n => harcLower n t

end PoincareConjecture.M28
