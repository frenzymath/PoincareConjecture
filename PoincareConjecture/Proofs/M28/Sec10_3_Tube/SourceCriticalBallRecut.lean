import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallPositiveEnd
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallScalarLimit
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.PositiveEndOrientation
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.PositiveEndRecutModel
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckRecutScalarModel











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 3200000 in






theorem exists_retained_smooth_recut_ambient_accuracy (R : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H),
        epsilon ≤ epsilon0 →
        ∀ (G : RegularPointedMetricConvergence
          (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
          (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ (D0 : LeviCivitaData G.limitMetric) (L : EpsilonNeck G.limitMetric),
            L.center = G.base → L.epsilon = 3 * epsilon / 2 → L.IsSeparating →
            ∀ X : Set G.limitCarrier.carrier, IsOpen X → IsConnected X →
              IsPreconnected Xᶜ → frontier X = L.central_sphere →
            ∀ (sigma : ℕ → ℕ), StrictMono sigma →
            ∀ (f : ℕ → UnitTwoSphere → ℝ),
              (∀ k, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f k)) →
              (∀ k z, |f k z| < epsilon⁻¹ / 32) →
              (∀ k, (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                W.high_index G (sigma k)) '' L.central_sphere =
                  range (fun z =>
                    ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
                      (z, f k z))) →
              (∀ x ∈ X, ∀ᶠ k in atTop, (G.embedding (sigma k) x).val.val ∉
                ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                  (f k)) →
              ∃ K : NeckOnlyCover G.limitMetric, K.X = X ∧ K.epsilon = 2 * epsilon ∧
                (∀ N ∈ K.necks, N.connection = D0) ∧
                ∃ T : CorrectedA19Conclusion G.limitMetric K,
                ∃ i ∈ T.tube.chain.shape.active,
                ∃ N : EpsilonNeck G.limitMetric,
                  N.SameUpToReversal (T.tube.chain.neck i) ∧ N.carrier ⊆ X ∧
                  ∃ P : Set G.limitCarrier.carrier,
                    IsOpen P ∧ IsConnected P ∧ P ⊆ X \ N.central_sphere ∧
                    closure P = P ∪ N.central_sphere ∧
                    ∃ a b : ℝ, -N.epsilon⁻¹ < a ∧ a < 0 ∧ 0 < b ∧ b < N.epsilon⁻¹ ∧
                    ∃ V : TopologicalSpace.Opens G.limitCarrier.carrier,
                      (V : Set G.limitCarrier.carrier) = P ∪ N.region a b ∧
                      (V : Set G.limitCarrier.carrier) ⊆ X ∧ N.central_sphere ⊆ V ∧
                      frontier (V : Set G.limitCarrier.carrier) =
                        N.coordinate_map '' (univ ×ˢ ({a} : Set ℝ)) ∧
                      (V : Set G.limitCarrier.carrier) \ P ⊆
                        N.coordinate_map '' (univ ×ˢ Icc a 0) ∧
                      ∃ B : OpenCylinderModel T.tube.carrier,
                        B.middleSphere = N.coordinate_map '' (univ ×ˢ ({a} : Set ℝ)) ∧
                        (V : Set G.limitCarrier.carrier) = B.tail true (1 / 2) ∧
                        SmoothSphereIsotopicIn T.tube.carrier
                          N.central_sphere T.tube.cylinder.middleSphere ∧
                        SmoothSphereIsotopicIn T.tube.carrier
                          B.middleSphere T.tube.cylinder.middleSphere ∧
                        closure (V : Set G.limitCarrier.carrier) ⊆ T.tube.carrier ∧
                        (∀ scalarBound : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
                          ∀ x ∈ T.tube.carrier, d < (B.inverse x).2 →
                            scalarBound < D0.scalarCurvature x) ∧
                      ∃ Z : OpenCylinderModel (V : Set G.limitCarrier.carrier),
                        (∀ x ∈ V, 3 ≤ D0.scalarCurvature x) ∧
                        (∃ B : ℝ, ∀ x ∈ Z.tail false (1 / 2), D0.scalarCurvature x ≤ B) ∧
                        (∀ B : ℝ, ∃ a ∈ Ioo (0 : ℝ) 1,
                          ∀ x ∈ Z.tail true a, B < D0.scalarCurvature x) ∧
                        ∀ x ∈ Z.tail true (1 / 2),
                          ∃ N' ∈ K.necks, N'.center = x ∧ N'.connection = D0 ∧
                            N'.carrier ⊆ V := by
  obtain ⟨epsilonE, hEpos, hEsmall, hend⟩ := exists_retained_positive_end_accuracy R
  obtain ⟨epsilonS, hSpos, _hSsmall, hscalar⟩ := exists_neck_recut_scalar_model_accuracy.{0}
  obtain ⟨epsilonL, hLpos, _hLsmall, hlower⟩ :=
    exists_source_criticalBall_limit_scalar_lower_accuracy.{u}
  refine ⟨min epsilonE (min (epsilonS / 2) epsilonL),
    lt_min hEpos (lt_min (half_pos hSpos) hLpos),
    (min_le_left _ _).trans hEsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let := G.limitCarrier.measurableSpace
  let := G.limitCarrier.borelSpace
  let := G.limitCarrier.t2Space
  let := G.limitCarrier.t3Space
  let : ConnectedSpace G.limitCarrier.carrier :=
    connectedSpace_iff_univ.mpr G.limitCarrier.connected
  intro D0 L hcenter hepsL hsep X hXo hXc hXcompl hfront sigma hsigma f hf hbound hgraphs hside
  obtain ⟨K, hKX, hKe, hKD, T, i, hi, hN0X, hN0sep,
      P, hPo, hPc, hPX, _hPf, hPcl, hcomponent, hcollar, _hcoords⟩ :=
    hend H W (hepsilon.trans (min_le_left _ _)) G D0 L hcenter hepsL hsep
      X hXo hXc hXcompl hfront sigma hsigma f hf hbound hgraphs hside
  obtain ⟨N, hsame, habove, hbelow⟩ :=
    (T.tube.chain.neck i).exists_orientation_into_component hN0sep hcomponent hcollar
  have hNX : N.carrier ⊆ X := by rw [hsame.carrier_eq]; exact hN0X
  have hPX' : P ⊆ X \ N.central_sphere := by rw [hsame.central_sphere_eq]; exact hPX
  have hPcl' : closure P = P ∪ N.central_sphere := by
    rw [hsame.central_sphere_eq]
    exact hPcl
  let a : ℝ := -N.epsilon⁻¹ / 4
  let b : ℝ := N.epsilon⁻¹ / 4
  have hNpos : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have ha : -N.epsilon⁻¹ < a := by dsimp [a]; linarith
  have ha0 : a < 0 := by dsimp [a]; linarith
  have hb0 : 0 < b := by dsimp [b]; linarith
  have hb : b < N.epsilon⁻¹ := by dsimp [b]; linarith
  obtain ⟨hVo, _hVc, hSV, hVfront, hVcl, _hVcomponent, hadded⟩ :=
    N.recut_positive_component hPo hPc hPcl' habove hbelow ha ha0 hb0 hb
  let V : TopologicalSpace.Opens G.limitCarrier.carrier := ⟨P ∪ N.region a b, hVo⟩
  have hVX : (V : Set G.limitCarrier.carrier) ⊆ X :=
    union_subset (fun _ hx => (hPX' hx).1) (fun _ hx => hNX hx.1)
  let U : TopologicalSpace.Opens G.limitCarrier.carrier :=
    ⟨T.tube.carrier, T.tube.carrier_open⟩
  have hXU : X ⊆ (U : Set G.limitCarrier.carrier) := hKX ▸ T.contains_X
  have hNU : N.carrier ⊆ (U : Set G.limitCarrier.carrier) := hNX.trans hXU
  have hPU : P ⊆ (U : Set G.limitCarrier.carrier) :=
    fun _ hx => hXU (hPX' hx).1
  have hisotopy : SmoothSphereIsotopicIn (U : Set G.limitCarrier.carrier)
      N.central_sphere T.tube.cylinder.middleSphere := by
    rw [hsame.central_sphere_eq]
    exact T.tube.central_sphere_isotopy i hi
  obtain ⟨B, hBS, hVB, _hmodel⟩ := exists_positive_recut_model (U := U)
    N T.tube.cylinder hNU hisotopy hPU hPo hPc hPcl' habove hbelow ha ha0 hb0 hb
  have hcut : N.coordinate_map '' (univ ×ˢ ({a} : Set ℝ)) =
      range (fun q : UnitTwoSphere => N.coordinate_map (q, a)) := by
    ext x
    constructor
    · rintro ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
      have hs' : s = a := hs
      exact ⟨q, by rw [hs']⟩
    · rintro ⟨q, rfl⟩
      exact ⟨(q, a), ⟨mem_univ _, rfl⟩, rfl⟩
  have hBisotopy : SmoothSphereIsotopicIn T.tube.carrier
      B.middleSphere T.tube.cylinder.middleSphere := by
    rw [hBS, hcut]
    exact ((neck_graph_isotopic_central N (fun _ => a) contMDiff_const
      (fun _ => ⟨ha, ha0.trans (hb0.trans hb)⟩)).mono_m28 hNU).trans hisotopy
  have hfrontCompact : IsCompact (frontier (V : Set G.limitCarrier.carrier)) := by
    change IsCompact (frontier (P ∪ N.region a b))
    rw [hVfront, ← hBS]
    exact B.isCompact_middleSphere
  have hclosureU : closure (V : Set G.limitCarrier.carrier) ⊆ U := by
    change closure (P ∪ N.region a b) ⊆ (U : Set G.limitCarrier.carrier)
    rw [hVcl]
    refine union_subset (hVX.trans hXU) ?_
    rintro x ⟨z, hz, rfl⟩
    apply hNU
    apply N.coordinate_map_mem_of_axial
    have hz' : z.2 = a := hz.2
    rw [hz']
    exact ⟨ha, ha0.trans hNpos⟩
  obtain ⟨volume, _hvolume, hvolumeBound⟩ := H.exists_criticalBall_limit_volume_bound
    W.tube W.radius W.radius_pos W.high_index G
  have hfinite : G.limitMetric.volumeMeasure univ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvolumeBound
  have hepsS : K.epsilon ≤ epsilonS := by
    rw [hKe]
    have hh := hepsilon.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hD : ∀ N' ∈ K.necks, N'.connection = D0 := fun N' hN' => (hKD N' hN').2
  have hBheight : Continuous (fun x : U => (B.inverse x).2) := continuous_snd.comp
    (B.inverse_smooth.continuousOn.comp_continuous continuous_subtype_val
      (fun x => x.property))
  have hBside (x : U) (hx : (1 / 2 : ℝ) < (B.inverse x).2) :
      x.val ∈ (V : Set G.limitCarrier.carrier) := by
    change x.val ∈ P ∪ N.region a b
    rw [hVB]
    exact (B.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr ⟨x.property, hx⟩
  have hBdiverge : ∀ scalarBound : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ x ∈ T.tube.carrier, d < (B.inverse x).2 →
        scalarBound < D0.scalarCurvature x := by
    intro scalarBound
    obtain ⟨d, hd, hd1, hhigh⟩ := scalar_diverges_on_proper_neck_cover_end
      K D0 hD hfinite (fun x : U => (B.inverse x).2) hBheight
      (fun x => (B.inverse_mem x x.property).2.2)
      (hVX.trans (by rw [hKX])) hclosureU hBside scalarBound
    exact ⟨d, hd, hd1, fun x hx hd' => hhigh ⟨x, hx⟩ hd'⟩
  obtain ⟨Z, hinit, hendScalar, hnecks⟩ := hscalar G.limitCarrier.carrier G.limitMetric
    D0 K hepsS hD hfinite U B V hVB hVo hfrontCompact
      (hVX.trans (by rw [hKX])) hclosureU
  refine ⟨K, hKX, hKe, hD, T, i, hi, N, hsame, hNX, P, hPo, hPc, hPX', hPcl',
    a, b, ha, ha0, hb0, hb, V, rfl, hVX, hSV, hVfront, hadded,
    B, hBS, hVB, hisotopy, hBisotopy, hclosureU, hBdiverge,
    Z, ?_, hinit, hendScalar, hnecks⟩
  intro x _hx
  have hh := hlower H W.tube
    (hepsilon.trans ((min_le_right _ _).trans (min_le_right _ _)))
    W.radius W.radius_pos W.high_index G D0 x
  have hm : (2 : ℝ) ≤ max C 2 := le_max_right _ _
  nlinarith

set_option maxHeartbeats 1600000 in





theorem exists_retained_smooth_recut_accuracy (R : RicciFlowCurvatureTheory.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E) (W : CriticalBallSourcePacket H),
        epsilon ≤ epsilon0 →
        ∀ (G : RegularPointedMetricConvergence
          (fun k => H.tubeCriticalMetric W.tube W.radius (W.high_index k))
          (fun k => H.tubeCriticalBase W.tube W.radius W.radius_pos (W.high_index k))),
          letI := G.limitCarrier.topologicalSpace
          letI := G.limitCarrier.chartedSpace
          letI := G.limitCarrier.isManifold
          ∀ (D0 : LeviCivitaData G.limitMetric) (L : EpsilonNeck G.limitMetric),
            L.center = G.base → L.epsilon = 3 * epsilon / 2 → L.IsSeparating →
            ∀ X : Set G.limitCarrier.carrier, IsOpen X → IsConnected X →
              IsPreconnected Xᶜ → frontier X = L.central_sphere →
            ∀ (sigma : ℕ → ℕ), StrictMono sigma →
            ∀ (f : ℕ → UnitTwoSphere → ℝ),
              (∀ k, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f k)) →
              (∀ k z, |f k z| < epsilon⁻¹ / 32) →
              (∀ k, (H.regularRawStageDiffeomorph W.tube W.radius W.radius_pos
                W.high_index G (sigma k)) '' L.central_sphere =
                  range (fun z =>
                    ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.coordinate_map
                      (z, f k z))) →
              (∀ x ∈ X, ∀ᶠ k in atTop, (G.embedding (sigma k) x).val.val ∉
                ((W.tube (W.high_index (G.subsequence (sigma k)))).list.node 0).2.belowGraph_m28
                  (f k)) →
              ∃ K : NeckOnlyCover G.limitMetric, K.X = X ∧ K.epsilon = 2 * epsilon ∧
                (∀ N ∈ K.necks, N.connection = D0) ∧
                ∃ T : CorrectedA19Conclusion G.limitMetric K,
                ∃ i ∈ T.tube.chain.shape.active,
                ∃ N : EpsilonNeck G.limitMetric,
                  N.SameUpToReversal (T.tube.chain.neck i) ∧ N.carrier ⊆ X ∧
                  ∃ P : Set G.limitCarrier.carrier,
                    IsOpen P ∧ IsConnected P ∧ P ⊆ X \ N.central_sphere ∧
                    closure P = P ∪ N.central_sphere ∧
                    ∃ a b : ℝ, -N.epsilon⁻¹ < a ∧ a < 0 ∧ 0 < b ∧ b < N.epsilon⁻¹ ∧
                    ∃ V : TopologicalSpace.Opens G.limitCarrier.carrier,
                      (V : Set G.limitCarrier.carrier) = P ∪ N.region a b ∧
                      (V : Set G.limitCarrier.carrier) ⊆ X ∧ N.central_sphere ⊆ V ∧
                      frontier (V : Set G.limitCarrier.carrier) =
                        N.coordinate_map '' (univ ×ˢ ({a} : Set ℝ)) ∧
                      (V : Set G.limitCarrier.carrier) \ P ⊆
                        N.coordinate_map '' (univ ×ˢ Icc a 0) ∧
                      ∃ Z : OpenCylinderModel (V : Set G.limitCarrier.carrier),
                        (∀ x ∈ V, 3 ≤ D0.scalarCurvature x) ∧
                        (∃ B : ℝ, ∀ x ∈ Z.tail false (1 / 2), D0.scalarCurvature x ≤ B) ∧
                        (∀ B : ℝ, ∃ a ∈ Ioo (0 : ℝ) 1,
                          ∀ x ∈ Z.tail true a, B < D0.scalarCurvature x) ∧
                        ∀ x ∈ Z.tail true (1 / 2),
                          ∃ N' ∈ K.necks, N'.center = x ∧ N'.connection = D0 ∧
                            N'.carrier ⊆ V := by
  obtain ⟨epsilon0, hpos, hsmall, hproduce⟩ :=
    exists_retained_smooth_recut_ambient_accuracy R
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro epsilon C A E H W hepsilon G
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  let := G.limitCarrier.measurableSpace
  let := G.limitCarrier.borelSpace
  let := G.limitCarrier.t2Space
  let := G.limitCarrier.t3Space
  intro D0 L hcenter hepsL hsep X hXo hXc hXcompl hfront sigma hsigma f hf hbound hgraphs hside
  obtain ⟨K, hKX, hKe, hD, T, i, hi, N, hsame, hNX, P, hPo, hPc, hPX, hPcl,
      a, b, ha, ha0, hb0, hb, V, hVeq, hVX, hSV, hVfront, hadded,
      _B, _hBS, _hVB, _hisotopy, _hBisotopy, _hclosure, _hBdiverge,
      Z, hscalar, hinit, hendScalar, hnecks⟩ :=
    hproduce H W hepsilon G D0 L hcenter hepsL hsep
      X hXo hXc hXcompl hfront sigma hsigma f hf hbound hgraphs hside
  exact ⟨K, hKX, hKe, hD, T, i, hi, N, hsame, hNX, P, hPo, hPc, hPX, hPcl,
    a, b, ha, ha0, hb0, hb, V, hVeq, hVX, hSV, hVfront, hadded,
    Z, hscalar, hinit, hendScalar, hnecks⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
