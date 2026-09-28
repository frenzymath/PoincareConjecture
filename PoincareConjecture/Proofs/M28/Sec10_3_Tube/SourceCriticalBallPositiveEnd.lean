import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallPositiveCover
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallLimitVolume
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceInitialSideNoncompact
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedPositiveSection
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.PositiveAmbientComponent
import PoincareConjecture.Proofs.M28.Generalized.NeckCoverEnd

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

set_option maxHeartbeats 3200000 in

theorem exists_retained_positive_end_accuracy (R : RicciFlowCurvatureTheory.{u}) :
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
                (∀ N ∈ K.necks, N.center ∈ X ∧ N.connection = D0) ∧
                ∃ T : CorrectedA19Conclusion G.limitMetric K,
                ∃ i ∈ T.tube.chain.shape.active,
                  (T.tube.chain.neck i).carrier ⊆ X ∧ (T.tube.chain.neck i).IsSeparating ∧
                  ∃ P : Set G.limitCarrier.carrier,
                    IsOpen P ∧ IsConnected P ∧ P ⊆ X \ (T.tube.chain.neck i).central_sphere ∧
                    frontier P = (T.tube.chain.neck i).central_sphere ∧
                    closure P = P ∪ (T.tube.chain.neck i).central_sphere ∧
                    (∀ x ∈ P,
                      connectedComponentIn (T.tube.chain.neck i).central_sphereᶜ x = P) ∧
                    ((T.tube.chain.neck i).belowGraph_m28 (fun _ => 0) ⊆ P ∨
                      (T.tube.chain.neck i).aboveGraph_m28 (fun _ => 0) ⊆ P) ∧
                    ∃ phi : T.tube.carrier ≃ₜ (UnitTwoSphere × Ioo (0 : ℝ) 1),
                      (∀ x : T.tube.carrier, cylinderSignedHeight phi x = 0 ↔
                        x.val ∈ (T.tube.chain.neck i).central_sphere) ∧
                      ∃ height : T.tube.carrier → ℝ, Continuous height ∧
                        (∀ x, 0 < height x ∧ height x < 1) ∧
                        (∀ x : T.tube.carrier, 1 / 2 < height x ↔ x.val ∈ P) ∧
                        ∀ B : ℝ, ∃ a : ℝ, 1 / 2 < a ∧ a < 1 ∧
                          ∀ x : T.tube.carrier, a < height x → B < D0.scalarCurvature x.val := by
  obtain ⟨epsilonC, hCpos, hCsmall, hcover⟩ := exists_retained_positive_side_tube_accuracy R
  obtain ⟨epsilonS, hSpos, _hSsmall, hselected⟩ :=
    exists_high_selected_neck_inside_accuracy.{0}
  refine ⟨min epsilonC (epsilonS / 2), lt_min hCpos (half_pos hSpos),
    (min_le_left _ _).trans hCsmall, ?_⟩
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
  intro D0 L hcenter hepsL hsep X hXopen hXconnected hXcompl hfront sigma hsigma
    f hf hbound hgraphs hside
  obtain ⟨K, hKX, hKe, hKD, ⟨T⟩⟩ :=
    hcover H W (hepsilon.trans (min_le_left _ _)) G D0 L hcenter hepsL hsep
      X hXconnected hfront sigma hsigma f hf hbound hgraphs hside
  have hD : ∀ N ∈ K.necks, N.connection = D0 := fun N hN => (hKD N hN).2
  obtain ⟨V, _hV, hvolume⟩ := H.exists_criticalBall_limit_volume_bound W.tube W.radius
    W.radius_pos W.high_index G
  have hfinite : G.limitMetric.volumeMeasure univ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvolume
  have hnoncompact : ¬ IsCompact (closure K.X) := by
    rw [hKX]
    exact H.not_isCompact_closure_retained_initial_side W G L X hXopen
      hXconnected.nonempty hfront sigma hsigma f hf hbound hgraphs
  have hunbounded := exists_scalar_gt_of_neck_cover_noncompact_closure K D0 hD hfinite
    hnoncompact
  have hKsmall : K.epsilon ≤ epsilonS := by
    rw [hKe]
    have hh := hepsilon.trans (min_le_right _ _)
    linarith
  have hKo : IsOpen K.X := hKX.symm ▸ hXopen
  have hKfront : IsCompact (frontier K.X) := by
    rw [hKX, hfront]
    exact L.isCompact_central_sphere
  obtain ⟨i, hi, _hhigh, hNX, hNsep⟩ :=
    hselected G.limitCarrier.carrier G.limitMetric D0 K T hKsmall hKo hKfront hunbounded 0
  let N := T.tube.chain.neck i
  let U : TopologicalSpace.Opens G.limitCarrier.carrier :=
    ⟨T.tube.carrier, T.tube.carrier_open⟩
  obtain ⟨P, phi, hPo, hPc, hPK, hPf, hPcl, hcomponent, hcollar, hzero, hhalf⟩ :=
    exists_positive_ambient_cylinder_half N hNsep hNX (hKX.symm ▸ hXcompl)
      U T.tube.cylinder T.contains_X (T.tube.central_sphere_isotopy i hi)
  have hclosure : closure P ⊆ (U : Set _) := by
    rw [hPcl]
    exact union_subset (fun _ hx => T.contains_X (hPK hx).1)
      (N.central_sphere_subset.trans (hNX.trans T.contains_X))
  have hPX : P ⊆ X \ N.central_sphere := by
    rw [← hKX]
    exact hPK
  have hheight : ∃ height : U → ℝ, Continuous height ∧
      (∀ x, 0 < height x ∧ height x < 1) ∧
      (∀ x : U, 1 / 2 < height x ↔ x.val ∈ P) := by
    let h : U → ℝ := fun x => ((phi x).2 : ℝ)
    have hc : Continuous h := continuous_subtype_val.comp (continuous_snd.comp phi.continuous)
    rcases hhalf with hnegative | hpositive
    · refine ⟨fun x => 1 - h x, continuous_const.sub hc, ?_, ?_⟩
      · intro x
        have hx := (phi x).2.property
        dsimp only [h]
        constructor <;> linarith [hx.1, hx.2]
      · intro x
        have heq : (1 / 2 : ℝ) < 1 - h x ↔ cylinderSignedHeight phi x < 0 := by
          dsimp only [h, cylinderSignedHeight]
          constructor <;> intro hx <;> linarith
        exact heq.trans (hnegative x)
    · refine ⟨h, hc, fun x => (phi x).2.property, ?_⟩
      intro x
      change (1 / 2 : ℝ) < ((phi x).2 : ℝ) ↔ x.val ∈ P
      exact sub_pos.symm.trans (hpositive x)
  obtain ⟨height, hh, hheightRange, hheightSide⟩ := hheight
  have hdiverges := scalar_diverges_on_proper_neck_cover_end K D0 hD hfinite height hh
    (fun x => (hheightRange x).2) (fun _ hx => (hPK hx).1) hclosure
    (fun x hx => (hheightSide x).mp hx)
  exact ⟨K, hKX, hKe, hKD, T, i, hi, hNX.trans hKX.subset, hNsep,
    P, hPo, hPc, hPX, hPf, hPcl, hcomponent, hcollar,
    phi, hzero, height, hh, hheightRange, hheightSide, hdiverges⟩

end PoincareConjecture.M28.CounterexampleNeckFamily
