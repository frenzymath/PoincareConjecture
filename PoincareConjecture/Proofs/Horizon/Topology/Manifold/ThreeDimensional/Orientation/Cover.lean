import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Orientation.Basic

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace Poincare.Topology.OrientationDoubleCover

variable (M : Type u) [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

noncomputable def transitionDet
    (i j : atlas (EuclideanSpace ℝ (Fin 3)) M) (x : M) : ℝ :=
  ((tangentBundleCore (𝓡 3) M).coordChange i j x).det

theorem transitionDet_self (i : atlas (EuclideanSpace ℝ (Fin 3)) M)
    (x : M) (hx : x ∈ (tangentBundleCore (𝓡 3) M).baseSet i) :
    transitionDet M i i x = 1 := by
  have hid : ((tangentBundleCore (𝓡 3) M).coordChange i i x).toLinearMap =
      LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact (tangentBundleCore (𝓡 3) M).coordChange_self i x hx v
  change LinearMap.det ((tangentBundleCore (𝓡 3) M).coordChange i i x).toLinearMap = 1
  rw [hid, LinearMap.det_id]

theorem transitionDet_comp (i j k : atlas (EuclideanSpace ℝ (Fin 3)) M)
    (x : M) (hx : x ∈ (tangentBundleCore (𝓡 3) M).baseSet i ∩
      (tangentBundleCore (𝓡 3) M).baseSet j ∩
      (tangentBundleCore (𝓡 3) M).baseSet k) :
    transitionDet M i k x = transitionDet M j k x * transitionDet M i j x := by
  dsimp only [transitionDet]
  rw [← (tangentBundleCore (𝓡 3) M).coordChange_linear_comp i j k x hx]
  exact LinearMap.det_comp _ _

theorem transitionDet_ne_zero (i j : atlas (EuclideanSpace ℝ (Fin 3)) M)
    (x : M) (hx : x ∈ (tangentBundleCore (𝓡 3) M).baseSet i ∩
      (tangentBundleCore (𝓡 3) M).baseSet j) :
    transitionDet M i j x ≠ 0 := by
  have hinverse := transitionDet_comp M i j i x ⟨hx, hx.1⟩
  rw [transitionDet_self M i x hx.1] at hinverse
  intro hzero
  rw [hzero, mul_zero] at hinverse
  exact one_ne_zero hinverse

noncomputable def core : FiberBundleCore (atlas (EuclideanSpace ℝ (Fin 3)) M) M Bool := by
  classical
  let Z := tangentBundleCore (𝓡 3) M
  have hsign (i j) : ContinuousOn (fun x => decide (transitionDet M i j x < 0))
      (Z.baseSet i ∩ Z.baseSet j) := by
    have hd : Continuous (fun x : ↑(Z.baseSet i ∩ Z.baseSet j) =>
        transitionDet M i j x) :=
      (ContinuousLinearMap.continuous_det.comp_continuousOn
        (Z.continuousOn_coordChange i j)).domRestrict
    rw [continuousOn_iff_continuous_domRestrict]
    apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    rcases lt_or_gt_of_ne (transitionDet_ne_zero M i j x x.2) with hneg | hpos
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
  exact {
    baseSet := Z.baseSet
    isOpen_baseSet := Z.isOpen_baseSet
    indexAt := Z.indexAt
    mem_baseSet_at := Z.mem_baseSet_at
    coordChange := fun i j x b => b ^^ decide (transitionDet M i j x < 0)
    coordChange_self := by
      intro i x hx b
      simp [transitionDet_self M i x hx, not_lt_of_gt (zero_lt_one : (0 : ℝ) < 1)]
    continuousOn_coordChange := by
      intro i j
      have hd : ContinuousOn (fun p : M × Bool => decide (transitionDet M i j p.1 < 0))
          ((Z.baseSet i ∩ Z.baseSet j) ×ˢ univ) :=
        (hsign i j).comp continuous_fst.continuousOn (fun _ hp => hp.1)
      exact (show Continuous (fun p : Bool × Bool => p.1 ^^ p.2) from
        continuous_of_discreteTopology).comp_continuousOn
          (continuous_snd.continuousOn.prodMk hd)
    coordChange_comp := by
      intro i j k x hx b
      rw [transitionDet_comp M i j k x hx,
        hmul _ _ (transitionDet_ne_zero M j k x ⟨hx.1.2, hx.2⟩)
          (transitionDet_ne_zero M i j x hx.1),
        Bool.xor_assoc, Bool.xor_comm (decide (transitionDet M j k x < 0))]
  }

theorem transitionDet_indexAt (i : atlas (EuclideanSpace ℝ (Fin 3)) M)
    (x : M) (hx : x ∈ i.1.source) :
    transitionDet M ((core M).indexAt x) i x =
      (mfderiv (𝓡 3) (𝓡 3) i.1 x).det := by
  unfold transitionDet
  congr 1
  rw [MDifferentiableAt.mfderiv (mdifferentiableAt_atlas (I := 𝓡 3) i.2 hx)]
  rfl

abbrev TotalSpace := (core M).TotalSpace

abbrev proj : TotalSpace M → M := fun p => p.proj

theorem isCoveringMap : IsCoveringMap (proj M) := FiberBundle.isCoveringMap

theorem proj_surjective : Function.Surjective (proj M) := fun x => ⟨⟨x, false⟩, rfl⟩

theorem isQuotientMap : IsQuotientMap (proj M) :=
  (isCoveringMap M).isQuotientMap (proj_surjective M)

theorem isCompact_preimage_of_subset_baseSet
    (i : atlas (EuclideanSpace ℝ (Fin 3)) M) {K : Set M}
    (hK : IsCompact K) (hKi : K ⊆ (core M).baseSet i) :
    IsCompact (proj M ⁻¹' K) := by
  let e := ((core M).localTriv i).toOpenPartialHomeomorph
  have hsub : K ×ˢ (univ : Set Bool) ⊆ e.target := fun _ hp => ⟨hKi hp.1, trivial⟩
  have heq : proj M ⁻¹' K = e.symm '' (K ×ˢ (univ : Set Bool)) := by
    ext p
    constructor
    · intro hp
      refine ⟨e p, ⟨hp, trivial⟩, e.left_inv (hKi hp)⟩
    · rintro ⟨q, hq, rfl⟩
      exact hq.1
  rw [heq]
  exact (hK.prod isCompact_univ).image_of_continuousOn (e.symm.continuousOn.mono hsub)

theorem compactSpace [CompactSpace M] : CompactSpace (TotalSpace M) := by
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M
  have hK (x : M) : ∃ K : Set M, IsCompact K ∧ x ∈ interior K ∧
      K ⊆ (core M).baseSet ((core M).indexAt x) :=
    exists_compact_subset ((core M).isOpen_baseSet _) ((core M).mem_baseSet_at x)
  choose K hcompact hmem hsub using hK
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => interior (K x)) (fun _ => isOpen_interior)
    (fun x _ => mem_iUnion.mpr ⟨x, hmem x⟩)
  have heq : (⋃ x ∈ s, proj M ⁻¹' K x) = (univ : Set (TotalSpace M)) := by
    apply eq_univ_of_forall
    intro p
    obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.mp (hs (mem_univ (proj M p)))
    exact mem_iUnion₂.mpr ⟨x, hx, show proj M p ∈ K x from interior_subset hpx⟩
  constructor
  rw [← heq]
  exact s.isCompact_biUnion fun x _ =>
    isCompact_preimage_of_subset_baseSet M ((core M).indexAt x) (hcompact x) (hsub x)

theorem nonempty_orientationCompatibleAtlas_of_section
    (s : C(M, TotalSpace M)) (hs : ∀ x, proj M (s x) = x) :
    Nonempty (PoincareConjecture.OrientationCompatibleAtlas M) := by
  classical
  let D := core M
  let Z := tangentBundleCore (𝓡 3) M
  let signs : ∀ i, Z.baseSet i → Bool := fun i x => (D.localTriv i (s x)).2
  refine ⟨{
    chartSign := signs
    chartSign_locallyConstant := ?_
    transition_positive := ?_
  }⟩
  · intro i
    apply (IsLocallyConstant.iff_continuous _).2
    exact continuous_snd.comp ((D.localTriv i).continuousOn.comp_continuous
      (s.continuous.comp continuous_subtype_val) (by
        intro x
        change proj M (s (x : M)) ∈ Z.baseSet i
        rw [hs]
        exact x.2))
  · intro i j x hi hj
    have hi' : (s x).proj ∈ D.baseSet i := by
      change proj M (s x) ∈ Z.baseSet i
      rwa [hs]
    have hj' : (s x).proj ∈ D.baseSet j := by
      change proj M (s x) ∈ Z.baseSet j
      rwa [hs]
    have hcoords := D.coordChange_comp (D.indexAt (s x).proj) i j
      (s x).proj ⟨⟨D.mem_baseSet_at _, hi'⟩, hj'⟩ (s x).2
    change ((D.localTriv i (s x)).2 ^^
      decide (transitionDet M i j (proj M (s x)) < 0)) =
        (D.localTriv j (s x)).2 at hcoords
    rw [hs] at hcoords
    have hpositive :
        0 < (if signs i ⟨x, hi⟩ = signs j ⟨x, hj⟩ then (1 : ℝ) else -1) *
          transitionDet M i j x := by
      change 0 < (if (D.localTriv i (s x)).2 =
        (D.localTriv j (s x)).2 then (1 : ℝ) else -1) * transitionDet M i j x
      rcases lt_or_gt_of_ne (transitionDet_ne_zero M i j x ⟨hi, hj⟩) with hneg | hpos
      · simp only [hneg, decide_true] at hcoords
        have hne : (D.localTriv i (s x)).2 ≠ (D.localTriv j (s x)).2 := by
          intro heq
          rw [← heq] at hcoords
          cases (D.localTriv i (s x)).2 <;> simp at hcoords
        simpa only [if_neg hne, neg_one_mul] using neg_pos.mpr hneg
      · have heq : (D.localTriv i (s x)).2 = (D.localTriv j (s x)).2 := by
          simpa [not_lt_of_gt hpos] using hcoords
        simpa only [if_pos heq, one_mul] using hpos
    simp only [transitionDet, tangentBundleCore_coordChange, mfderiv_eq_fderiv, mfld_simps,
      fderivWithin_univ, ContinuousLinearMap.det, Function.comp_def] at hpositive ⊢
    convert! hpositive

def flip (p : TotalSpace M) : TotalSpace M := ⟨p.proj, !p.2⟩

@[simp] theorem proj_flip (p : TotalSpace M) : proj M (flip M p) = proj M p := rfl

@[simp] theorem flip_flip (p : TotalSpace M) : flip M (flip M p) = p := by
  rcases p with ⟨x, b⟩
  cases b <;> rfl

theorem flip_ne_self (p : TotalSpace M) : flip M p ≠ p := by
  intro h
  have h' : Bool.not p.2 = p.2 := congrArg (fun q : TotalSpace M => q.2) h
  have hn (b : Bool) : Bool.not b ≠ b := by cases b <;> decide
  exact hn p.2 h'

@[simp] theorem localTriv_flip (i : atlas (EuclideanSpace ℝ (Fin 3)) M)
    (p : TotalSpace M) :
    ((core M).localTriv i (flip M p)).2 = !((core M).localTriv i p).2 := by
  classical
  change ((!p.2) ^^ decide (transitionDet M ((core M).indexAt p.proj) i p.proj < 0)) =
    !(p.2 ^^ decide (transitionDet M ((core M).indexAt p.proj) i p.proj < 0))
  cases p.2 <;>
    cases decide (transitionDet M ((core M).indexAt p.proj) i p.proj < 0) <;> rfl

theorem continuous_flip : Continuous (flip M) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply (FiberBundle.continuousAt_totalSpace Bool (flip M)).2
  refine ⟨(core M).continuous_proj.continuousAt, ?_⟩
  change ContinuousAt (fun q => ((core M).localTriv ((core M).indexAt p.proj)
    (flip M q)).2) p
  simp only [localTriv_flip]
  exact (show Continuous (fun b : Bool => !b) from continuous_of_discreteTopology).continuousAt.comp
    (continuous_snd.continuousAt.comp
      (((core M).localTrivAt p.proj).continuousAt (by
        change p.proj ∈ (core M).baseSet ((core M).indexAt p.proj)
        exact (core M).mem_baseSet_at p.proj)))

noncomputable def flipHomeomorph : TotalSpace M ≃ₜ TotalSpace M where
  toFun := flip M
  invFun := flip M
  left_inv := flip_flip M
  right_inv := flip_flip M
  continuous_toFun := continuous_flip M
  continuous_invFun := continuous_flip M

private theorem continuous_fiberDescend {Y : Type*} [TopologicalSpace Y]
    (f : TotalSpace M → Y) (hf : Continuous f)
    (hflip : ∀ p, f (flip M p) = f p) :
    Continuous (fun x => f (⟨x, false⟩ : TotalSpace M)) := by
  apply (isQuotientMap M).continuous_iff.mpr
  have heq : (fun x => f (⟨x, false⟩ : TotalSpace M)) ∘ proj M = f := by
    funext p
    rcases p with ⟨x, b⟩
    cases b
    · rfl
    · exact (hflip ⟨x, false⟩).symm
  rwa [heq]

theorem nonempty_orientationCompatibleAtlas_of_flip_separating
    (f : TotalSpace M → Bool) (hf : Continuous f)
    (hflip : ∀ p, f (flip M p) ≠ f p) :
    Nonempty (PoincareConjecture.OrientationCompatibleAtlas M) := by
  classical
  let select : TotalSpace M → TotalSpace M := fun p => if f p then flip M p else p
  have hc : IsClopen {p : TotalSpace M | f p = true} :=
    (isClopen_discrete {true}).preimage hf
  have hcont : Continuous select := by
    apply Continuous.if _ (continuous_flip M) continuous_id
    intro p hp
    simp [hc.frontier_eq] at hp
  have hinv (p : TotalSpace M) : select (flip M p) = select p := by
    have hp := hflip p
    cases h0 : f p <;> cases h1 : f (flip M p) <;>
      simp_all [select]
  let s : C(M, TotalSpace M) :=
    ⟨fun x => select (⟨x, false⟩ : TotalSpace M),
      continuous_fiberDescend M select hcont hinv⟩
  apply nonempty_orientationCompatibleAtlas_of_section M s
  intro x
  change proj M (select ⟨x, false⟩) = x
  dsimp [select]
  split <;> rfl

theorem connectedSpace_of_not_nonempty_orientationCompatibleAtlas [ConnectedSpace M]
    (hno : ¬ Nonempty (PoincareConjecture.OrientationCompatibleAtlas M)) :
    ConnectedSpace (TotalSpace M) := by
  classical
  have hpre : PreconnectedSpace (TotalSpace M) := by
    apply preconnectedSpace_of_forall_constant
    intro f hf p q
    let parity : TotalSpace M → Bool := fun r => f r ^^ f (flip M r)
    have hparity : Continuous parity :=
      (show Continuous (fun b : Bool × Bool => b.1 ^^ b.2) from
        continuous_of_discreteTopology).comp (hf.prodMk (hf.comp (continuous_flip M)))
    have hinv (r : TotalSpace M) : parity (flip M r) = parity r := by
      simp only [parity, flip_flip, Bool.xor_comm]
    let g : M → Bool := fun x => parity (⟨x, false⟩ : TotalSpace M)
    have hg : Continuous g := continuous_fiberDescend M parity hparity hinv
    have hg_eq (r : TotalSpace M) : g (proj M r) = parity r := by
      rcases r with ⟨x, b⟩
      cases b
      · rfl
      · exact (hinv ⟨x, false⟩).symm
    have hconstant (r : TotalSpace M) : parity r = parity p := by
      rw [← hg_eq r, ← hg_eq p]
      exact ((IsLocallyConstant.iff_continuous _).mpr hg).apply_eq_of_preconnectedSpace _ _
    cases hp : parity p
    · have hsame (r : TotalSpace M) : f (flip M r) = f r := by
        have hr : (f r ^^ f (flip M r)) = false := (hconstant r).trans hp
        cases h0 : f r <;> cases h1 : f (flip M r) <;> simp_all
      have hbase : Continuous (fun x => f (⟨x, false⟩ : TotalSpace M)) :=
        continuous_fiberDescend M f hf hsame
      have hdesc (r : TotalSpace M) : f (⟨proj M r, false⟩ : TotalSpace M) = f r := by
        rcases r with ⟨x, b⟩
        cases b
        · rfl
        · exact (hsame ⟨x, false⟩).symm
      rw [← hdesc p, ← hdesc q]
      exact ((IsLocallyConstant.iff_continuous _).mpr hbase).apply_eq_of_preconnectedSpace _ _
    · exfalso
      apply hno (nonempty_orientationCompatibleAtlas_of_flip_separating M f hf _)
      intro r heq
      have hr : (f r ^^ f (flip M r)) = true := (hconstant r).trans hp
      rw [heq, Bool.xor_self] at hr
      contradiction
  let := hpre
  exact ⟨⟨⟨Classical.choice (inferInstance : Nonempty M), false⟩⟩⟩

end Poincare.Topology.OrientationDoubleCover
