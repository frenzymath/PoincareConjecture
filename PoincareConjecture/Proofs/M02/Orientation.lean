import PoincareConjecture.Definitions.Ch01.Topology










set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M02



theorem nonempty_orientationCompatibleAtlas
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [SimplyConnectedSpace M] :
    Nonempty (PoincareConjecture.OrientationCompatibleAtlas M) := by
  classical
  let Z := tangentBundleCore (𝓡 3) M
  let det := fun (i j : atlas (EuclideanSpace ℝ (Fin 3)) M) (x : M) =>
    (Z.coordChange i j x).det
  have hself (i) (x : M) (hx : x ∈ Z.baseSet i) : det i i x = 1 := by
    have hid : (Z.coordChange i i x).toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro v
      exact Z.coordChange_self i x hx v
    change LinearMap.det (Z.coordChange i i x).toLinearMap = 1
    rw [hid, LinearMap.det_id]
  have hcomp (i j k) (x : M)
      (hx : x ∈ Z.baseSet i ∩ Z.baseSet j ∩ Z.baseSet k) :
      det i k x = det j k x * det i j x := by
    dsimp only [det]
    rw [← Z.coordChange_linear_comp i j k x hx]
    exact LinearMap.det_comp _ _
  have hnonzero (i j) (x : M) (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) :
      det i j x ≠ 0 := by
    have hinverse := hcomp i j i x ⟨hx, hx.1⟩
    rw [hself i x hx.1] at hinverse
    intro hzero
    rw [hzero, mul_zero] at hinverse
    exact one_ne_zero hinverse

  have hsign (i j) : ContinuousOn (fun x => decide (det i j x < 0))
      (Z.baseSet i ∩ Z.baseSet j) := by
    have hd : Continuous (fun x : ↑(Z.baseSet i ∩ Z.baseSet j) => det i j x) :=
      (ContinuousLinearMap.continuous_det.comp_continuousOn
        (Z.continuousOn_coordChange i j)).domRestrict
    rw [continuousOn_iff_continuous_domRestrict]
    apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    rcases lt_or_gt_of_ne (hnonzero i j x x.2) with hneg | hpos
    · filter_upwards [Filter.Tendsto.eventually_lt_const hneg hd.continuousAt] with y hy
      simp [Set.domRestrict, hneg, hy]
    · filter_upwards [Filter.Tendsto.eventually_const_lt hpos hd.continuousAt] with y hy
      simp [Set.domRestrict, not_lt_of_gt hpos, not_lt_of_gt hy]
  have hmul (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
      decide (a * b < 0) = (decide (a < 0) ^^ decide (b < 0)) := by
    rcases lt_or_gt_of_ne ha with ha | ha <;>
      rcases lt_or_gt_of_ne hb with hb | hb
    · simp [ha, hb, not_lt_of_gt (mul_pos_of_neg_of_neg ha hb)]
    · simp [ha, not_lt_of_gt hb, mul_neg_of_neg_of_pos ha hb]
    · simp [not_lt_of_gt ha, hb, mul_neg_of_pos_of_neg ha hb]
    · simp [not_lt_of_gt ha, not_lt_of_gt hb, not_lt_of_gt (mul_pos ha hb)]

  let D : FiberBundleCore (atlas (EuclideanSpace ℝ (Fin 3)) M) M Bool := {
    baseSet := Z.baseSet
    isOpen_baseSet := Z.isOpen_baseSet
    indexAt := Z.indexAt
    mem_baseSet_at := Z.mem_baseSet_at
    coordChange := fun i j x b => b ^^ decide (det i j x < 0)
    coordChange_self := by
      intro i x hx b
      simp [hself i x hx, not_lt_of_gt (zero_lt_one : (0 : ℝ) < 1)]
    continuousOn_coordChange := by
      intro i j
      have hd : ContinuousOn (fun p : M × Bool => decide (det i j p.1 < 0))
          ((Z.baseSet i ∩ Z.baseSet j) ×ˢ univ) :=
        (hsign i j).comp continuous_fst.continuousOn (fun _ hp => hp.1)
      exact (show Continuous (fun p : Bool × Bool => p.1 ^^ p.2) from
        continuous_of_discreteTopology).comp_continuousOn
          (continuous_snd.continuousOn.prodMk hd)
    coordChange_comp := by
      intro i j k x hx b
      rw [hcomp i j k x hx,
        hmul _ _ (hnonzero j k x ⟨hx.1.2, hx.2⟩) (hnonzero i j x hx.1),
        Bool.xor_assoc, Bool.xor_comm (decide (det j k x < 0))]
  }
  let : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  have hcover : IsCoveringMap D.proj := FiberBundle.isCoveringMap
  let x0 : M := Classical.choice ((simply_connected_iff_unique_homotopic M).mp
    inferInstance).1
  obtain ⟨sectionMap, hsection, _⟩ := hcover.existsUnique_continuousMap_lifts
    (ContinuousMap.id M) x0 (⟨x0, false⟩ : D.TotalSpace) rfl
  have hproj (x : M) : (sectionMap x).proj = x := congrFun hsection.2 x
  let signs : ∀ i, Z.baseSet i → Bool :=
    fun i x => (D.localTriv i (sectionMap x)).2
  refine ⟨{
    chartSign := signs
    chartSign_locallyConstant := ?_
    transition_positive := ?_
  }⟩
  · intro i
    apply (IsLocallyConstant.iff_continuous _).2
    exact continuous_snd.comp ((D.localTriv i).continuousOn.comp_continuous
      (sectionMap.continuous.comp continuous_subtype_val) (by
        intro x
        change (sectionMap (x : M)).proj ∈ Z.baseSet i
        rw [hproj]
        exact x.2))
  · intro i j x hi hj
    have hi' : (sectionMap x).proj ∈ D.baseSet i := by
      change (sectionMap x).proj ∈ Z.baseSet i
      rwa [hproj]
    have hj' : (sectionMap x).proj ∈ D.baseSet j := by
      change (sectionMap x).proj ∈ Z.baseSet j
      rwa [hproj]
    have hcoords := D.coordChange_comp (D.indexAt (sectionMap x).proj) i j
      (sectionMap x).proj ⟨⟨D.mem_baseSet_at _, hi'⟩, hj'⟩ (sectionMap x).2
    change ((D.localTriv i (sectionMap x)).2 ^^
      decide (det i j (sectionMap x).proj < 0)) =
        (D.localTriv j (sectionMap x)).2 at hcoords
    rw [hproj] at hcoords
    have hpositive :
        0 < (if signs i ⟨x, hi⟩ = signs j ⟨x, hj⟩ then (1 : ℝ) else -1) *
          det i j x := by
      change 0 < (if (D.localTriv i (sectionMap x)).2 =
        (D.localTriv j (sectionMap x)).2 then (1 : ℝ) else -1) * det i j x
      rcases lt_or_gt_of_ne (hnonzero i j x ⟨hi, hj⟩) with hneg | hpos
      · simp only [hneg, decide_true] at hcoords
        have hne : (D.localTriv i (sectionMap x)).2 ≠
            (D.localTriv j (sectionMap x)).2 := by
          intro heq
          rw [← heq] at hcoords
          cases (D.localTriv i (sectionMap x)).2 <;> simp at hcoords
        simpa only [if_neg hne, neg_one_mul] using neg_pos.mpr hneg
      · have heq : (D.localTriv i (sectionMap x)).2 =
            (D.localTriv j (sectionMap x)).2 := by
          simpa [not_lt_of_gt hpos] using hcoords
        simpa only [if_pos heq, one_mul] using hpos
    simp only [det, Z, tangentBundleCore_coordChange, mfderiv_eq_fderiv, mfld_simps,
      fderivWithin_univ, ContinuousLinearMap.det, Function.comp_def] at hpositive ⊢
    convert! hpositive

end PoincareConjecture.Proofs.M02
