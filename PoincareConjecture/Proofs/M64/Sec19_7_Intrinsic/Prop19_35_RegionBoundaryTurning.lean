import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingLoss
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.EdgeGeometry
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology Manifold ContDiff intervalIntegral
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem arc_endpoint_set_eq_of_image_eq
    {gamma eta : ℝ → AnnulusCoordinates} {a b : ℝ}
    (hgammaCont : ContinuousOn gamma (Icc a b))
    (hgammaInj : InjOn gamma (Icc a b))
    (hetaCont : ContinuousOn eta (Icc (0 : ℝ) 1))
    (hetaInj : InjOn eta (Icc (0 : ℝ) 1))
    (himage : eta '' Icc (0 : ℝ) 1 = gamma '' Icc a b) :
    ({eta 0, eta 1} : Set AnnulusCoordinates) = {gamma a, gamma b} := by
  let phi : ℝ → ℝ := fun t => Function.invFunOn gamma (Icc a b) (eta t)
  have hpre (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ∃ s ∈ Icc a b, gamma s = eta t := by
    have htImage : eta t ∈ gamma '' Icc a b := by
      rw [← himage]
      exact mem_image_of_mem eta ht
    obtain ⟨s, hs, hst⟩ := htImage
    exact ⟨s, hs, hst⟩
  have hmap : MapsTo phi (Icc (0 : ℝ) 1) (Icc a b) :=
    fun t ht => Function.invFunOn_mem (hpre t ht)
  have heq : EqOn eta (gamma ∘ phi) (Icc (0 : ℝ) 1) :=
    fun t ht => (Function.invFunOn_eq (hpre t ht)).symm
  let H : Icc a b ≃ₜ gamma '' Icc a b :=
    Continuous.homeoOfEquivCompactToT2
      (f := Equiv.Set.imageOfInjOn gamma (Icc a b) hgammaInj)
      (hgammaCont.domRestrict.subtype_mk _)
  let etaImage : Icc (0 : ℝ) 1 → gamma '' Icc a b :=
    fun t => ⟨eta t, by rw [← himage]; exact mem_image_of_mem eta t.property⟩
  have hetaImage : Continuous etaImage := hetaCont.domRestrict.subtype_mk _
  have hphiEq (t : Icc (0 : ℝ) 1) : phi t = (H.symm (etaImage t)).val := by
    apply hgammaInj (hmap t.property) (H.symm (etaImage t)).property
    have hH := congrArg Subtype.val (H.apply_symm_apply (etaImage t))
    exact (heq t.property).symm.trans hH.symm
  have hphiCont : ContinuousOn phi (Icc (0 : ℝ) 1) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hfun : (Icc (0 : ℝ) 1).domRestrict phi =
        fun t => (H.symm (etaImage t)).val := funext hphiEq
    rw [hfun]
    exact continuous_subtype_val.comp (H.symm.continuous.comp hetaImage)
  have hphiInj : InjOn phi (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    apply hetaInj hs ht
    exact (heq hs).trans ((congrArg gamma hst).trans (heq ht).symm)
  have hphiSurj : SurjOn phi (Icc (0 : ℝ) 1) (Icc a b) := by
    intro s hs
    have hsImage : gamma s ∈ eta '' Icc (0 : ℝ) 1 := by
      rw [himage]
      exact mem_image_of_mem gamma hs
    obtain ⟨t, ht, hts⟩ := hsImage
    refine ⟨t, ht, ?_⟩
    apply hgammaInj (hmap ht) hs
    exact (heq ht).symm.trans hts
  have hphiImage : phi '' Icc (0 : ℝ) 1 = Icc a b := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact hmap ht
    · exact hphiSurj
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hetaZero : eta 0 = gamma (phi 0) := heq hzero
  have hetaOne : eta 1 = gamma (phi 1) := heq hone
  rcases hphiCont.strictMonoOn_of_injOn_Icc' zero_le_one hphiInj with hmono | hanti
  · have hinterval : Icc (phi 0) (phi 1) = Icc a b :=
      (hphiCont.image_Icc_of_monotoneOn zero_le_one hmono.monotoneOn).symm.trans hphiImage
    have hends := (Icc_eq_Icc_iff
      (hmono.monotoneOn hzero hone zero_le_one)).mp hinterval
    rw [hetaZero, hetaOne, hends.1, hends.2]
  · have hinterval : Icc (phi 1) (phi 0) = Icc a b :=
      (hphiCont.image_Icc_of_antitoneOn zero_le_one hanti.antitoneOn).symm.trans hphiImage
    have hends := (Icc_eq_Icc_iff
      (hanti.antitoneOn hzero hone zero_le_one)).mp hinterval
    rw [hetaZero, hetaOne, hends.2, hends.1, pair_comm]

private theorem sum_disjoint_turning_le_interval
    {A : Type*} (N : IntrinsicAnnulus) (T : Finset A)
    {lo hi : A → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hbounds : ∀ p ∈ T, a ≤ lo p ∧ lo p ≤ hi p ∧ hi p ≤ b)
    (hdisj : (T : Set A).PairwiseDisjoint (fun p => Ioo (lo p) (hi p))) :
    (∑ p ∈ T, intrinsicGeodesicCurvatureIntegral
      N.metric N.connection 1 (lo p) (hi p)) ≤
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b := by
  classical
  let density : ℝ → ℝ := fun s =>
    intrinsicGeodesicCurvature N.metric N.connection 1 s *
      intrinsicBoundarySpeed N.metric 1 s
  have hdensity : Continuous density :=
    m64Intrinsic_continuous_turning_density N (by norm_num : (1 : ℝ) ≠ 0)
  have hint : IntegrableOn density (Ioc a b) :=
    hdensity.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hsub (p : A) (hp : p ∈ T) : Ioc (lo p) (hi p) ⊆ Ioc a b := by
    intro s hs
    exact ⟨(hbounds p hp).1.trans_lt hs.1, hs.2.trans (hbounds p hp).2.2⟩
  have hdisj' : (T : Set A).PairwiseDisjoint (fun p => Ioc (lo p) (hi p)) := by
    intro p hp q hq hpq
    exact Ioc_disjoint_Ioc.mpr (Ioo_disjoint_Ioo.mp (hdisj hp hq hpq))
  have hunion : (⋃ p ∈ T, Ioc (lo p) (hi p)) ⊆ Ioc a b := by
    intro s hs
    obtain ⟨p, hs⟩ := mem_iUnion.mp hs
    obtain ⟨hp, hs⟩ := mem_iUnion.mp hs
    exact hsub p hp hs
  have hsum := integral_biUnion_finset T
    (fun _ _ => measurableSet_Ioc) hdisj'
    (fun p hp => hint.mono_set (hsub p hp))
  have hmono : (∫ s in ⋃ p ∈ T, Ioc (lo p) (hi p), density s) ≤
      ∫ s in Ioc a b, density s := by
    apply setIntegral_mono_set hint
    · exact Filter.Eventually.of_forall (fun s =>
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    · exact Filter.Eventually.of_forall (fun s hs => hunion hs)
  rw [hsum] at hmono
  change (∑ p ∈ T, intrinsicGeodesicCurvatureIntegral
    N.metric N.connection 1 (lo p) (hi p)) ≤ _
  calc
    _ = ∑ p ∈ T, ∫ s in Ioc (lo p) (hi p), density s := by
      apply Finset.sum_congr rfl
      intro p hp
      exact intervalIntegral.integral_of_le (hbounds p hp).2.1
    _ ≤ ∫ s in Ioc a b, density s := hmono
    _ = intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b := by
      exact (intervalIntegral.integral_of_le hab).symm

theorem m64Intrinsic_region_boundary_side_intervals_disjoint_turning_le
    {I : Type*} (N : IntrinsicAnnulus)
    (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (basis : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : ∀ i, convexHull ℝ (range (basis i)) ⊆ (F i).source)
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (basis i (k.succAbove 0)) (basis i (k.succAbove 1)))
    (hinj : ∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1))
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ w : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (basis i w)})
    {a b : ℝ} (hab : a ≤ b) (gamma : ℝ → AnnulusCoordinates)
    (hgammaCont : ContinuousOn gamma (Icc a b))
    (hgammaInj : InjOn gamma (Icc a b))
    (T : Finset (I × Fin 3)) (lo hi : I × Fin 3 → ℝ)
    (hbounds : ∀ p ∈ T, a ≤ lo p ∧ lo p < hi p ∧ hi p ≤ b)
    (hunpaired : ∀ p ∈ T, ∀ q : I × Fin 3,
      faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p)
    (himage : ∀ p ∈ T, ((face p.1).boundary p.2).map '' Icc (0 : ℝ) 1 =
      gamma '' Icc (lo p) (hi p)) :
    (T : Set (I × Fin 3)).PairwiseDisjoint (fun p => Ioo (lo p) (hi p)) ∧
      (∑ p ∈ T, intrinsicGeodesicCurvatureIntegral
        N.metric N.connection 1 (lo p) (hi p)) ≤
          intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b := by
  classical
  let side : I × Fin 3 → ℝ → AnnulusCoordinates :=
    fun p => ((face p.1).boundary p.2).map
  have hends (p : I × Fin 3) (hp : p ∈ T) :
      ({side p 0, side p 1} : Set AnnulusCoordinates) =
        {gamma (lo p), gamma (hi p)} := by
    have hsub : Icc (lo p) (hi p) ⊆ Icc a b :=
      Icc_subset_Icc (hbounds p hp).1 (hbounds p hp).2.2
    exact arc_endpoint_set_eq_of_image_eq
      (hgammaCont.mono hsub) (hgammaInj.mono hsub)
      ((face p.1).boundary p.2).smooth.continuousOn (hinj p.1 p.2)
      (himage p hp)
  have hpair : (T : Set (I × Fin 3)).PairwiseDisjoint
      (fun p => Ioo (lo p) (hi p)) := by
    intro p hp q hq hpq
    apply disjoint_left.mpr
    intro x hxp hxq
    have hpSub : Icc (lo p) (hi p) ⊆ Icc a b :=
      Icc_subset_Icc (hbounds p hp).1 (hbounds p hp).2.2
    have hne : side p '' Icc (0 : ℝ) 1 ≠ side q '' Icc (0 : ℝ) 1 := by
      intro heq
      have hedge := (faceBoundaryIndex_eq_iff face p.1 q.1 p.2 q.2).mpr heq
      exact hpq (hunpaired p hp q hedge.symm).symm
    have hcommon : gamma x ∈
        side p '' Icc (0 : ℝ) 1 ∩ side q '' Icc (0 : ℝ) 1 := by
      constructor
      · rw [himage p hp]
        exact mem_image_of_mem gamma (Ioo_subset_Icc_self hxp)
      · rw [himage q hq]
        exact mem_image_of_mem gamma (Ioo_subset_Icc_self hxq)
    have hxend := Euler.coordinate_cover_edge_meet face F basis hsource hboundary hinj hinter
      p.1 q.1 p.2 q.2 hne hcommon
    change gamma x ∈ ({side p 0, side p 1} : Set AnnulusCoordinates) at hxend
    rw [hends p hp] at hxend
    rcases Set.mem_insert_iff.mp hxend with hxlo | hxhi
    · have heq := hgammaInj (hpSub (Ioo_subset_Icc_self hxp))
        (hpSub (left_mem_Icc.mpr (hbounds p hp).2.1.le)) hxlo
      exact hxp.1.ne' heq
    · have heq := hgammaInj (hpSub (Ioo_subset_Icc_self hxp))
        (hpSub (right_mem_Icc.mpr (hbounds p hp).2.1.le))
        (mem_singleton_iff.mp hxhi)
      exact hxp.2.ne heq
  refine ⟨hpair, ?_⟩
  exact sum_disjoint_turning_le_interval N T hab
    (fun p hp => ⟨(hbounds p hp).1, (hbounds p hp).2.1.le, (hbounds p hp).2.2⟩) hpair

end PoincareConjecture
