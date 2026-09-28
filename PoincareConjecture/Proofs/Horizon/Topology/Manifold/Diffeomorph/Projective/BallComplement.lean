import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Projective.Gluing
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Projective.Covering
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BallImages
import PoincareConjecture.Proofs.Horizon.Topology.Maps.OpenPartialHomeomorph.Compact
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere

noncomputable section
set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.ProjectiveGluing

open PoincareConjecture

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

theorem mem_neg_image (A : Set UnitThreeSphere) (x : UnitThreeSphere) :
    x ∈ Neg.neg '' A ↔ -x ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [neg_neg] using hy
  · intro hx
    exact ⟨-x, hx, neg_neg x⟩

theorem mem_antipodalBallComplement (b : OpenPartialHomeomorph E3 UnitThreeSphere)
    (x : UnitThreeSphere) :
    x ∈ antipodalBallComplement b ↔
      x ∉ b '' Metric.ball 0 1 ∧ -x ∉ b '' Metric.ball 0 1 := by
  simp only [antipodalBallComplement, mem_compl_iff, mem_union, mem_neg_image, not_or]

theorem neg_mem_antipodalBallComplement (b : OpenPartialHomeomorph E3 UnitThreeSphere)
    (x : UnitThreeSphere) : -x ∈ antipodalBallComplement b ↔ x ∈ antipodalBallComplement b := by
  simp only [mem_antipodalBallComplement, neg_neg, and_comm]

theorem antipodalBallComplement_avoids_puncture
    {p : RealProjectiveThree} (a : UnitThreeSphere) (ha : Quotient.mk' a = p)
    (b : OpenPartialHomeomorph E3 UnitThreeSphere) (hb0 : b 0 = a)
    {x : UnitThreeSphere} (hx : x ∈ antipodalBallComplement b) : Quotient.mk' x ≠ p := by
  have haA : a ∈ b '' Metric.ball 0 1 :=
    hb0 ▸ mem_image_of_mem b (Metric.mem_ball_self (by norm_num))
  intro hxp
  rcases Quotient.exact (hxp.trans ha.symm) with h | h
  · exact ((mem_antipodalBallComplement b x).mp hx).1 (h.symm ▸ haA)
  · exact ((mem_antipodalBallComplement b x).mp hx).2 (by simpa only [h, neg_neg] using haA)

theorem antipodalBallComplement_topology
    (b : OpenPartialHomeomorph E3 UnitThreeSphere)
    (hbs : Metric.closedBall 0 1 ⊆ b.source)
    (hBB : Disjoint (b '' Metric.closedBall 0 1)
      (Neg.neg '' (b '' Metric.closedBall 0 1))) :
    IsCompact (antipodalBallComplement b) ∧
    interior (antipodalBallComplement b) =
      (b '' Metric.closedBall 0 1 ∪ Neg.neg '' (b '' Metric.closedBall 0 1))ᶜ ∧
    closure (interior (antipodalBallComplement b)) = antipodalBallComplement b ∧
    frontier (antipodalBallComplement b) =
      b '' Metric.sphere 0 1 ∪ Neg.neg '' (b '' Metric.sphere 0 1) := by
  let A := b '' Metric.ball 0 1
  let B := b '' Metric.closedBall 0 1
  have hBc : IsCompact B := (isCompact_closedBall (0 : E3) 1).image_of_continuousOn
    (b.continuousOn.mono hbs)
  have hA : IsOpen A :=
    b.isOpen_image_of_subset_source Metric.isOpen_ball (Metric.ball_subset_closedBall.trans hbs)
  have hnA : IsOpen (Neg.neg '' A) := (Homeomorph.neg UnitThreeSphere).isOpenMap _ hA
  have hK : IsClosed (antipodalBallComplement b) := (hA.union hnA).isClosed_compl
  have hiB : interior B = A := (b.image_ball_eq_interior hbs rfl).symm
  have hfB : frontier B = b '' Metric.sphere 0 1 := (b.image_sphere_eq_frontier hbs rfl).symm
  have hclA : closure A = B := by
    have h := (b.image_region_of_isCompact_closure
      (D := Metric.ball (0 : E3) 1) Metric.isOpen_ball
      (by simpa only [closure_ball (0 : E3) (by norm_num : (1 : ℝ) ≠ 0)] using
        isCompact_closedBall (0 : E3) 1)
      (by simpa only [closure_ball (0 : E3) (by norm_num : (1 : ℝ) ≠ 0)] using hbs)).2.2.1
    simpa only [closure_ball (0 : E3) (by norm_num : (1 : ℝ) ≠ 0)] using h
  have hnclA : closure (Neg.neg '' A) = Neg.neg '' B := by
    have h : Neg.neg '' closure A = closure (Neg.neg '' A) :=
      (Homeomorph.neg UnitThreeSphere).image_closure A
    rw [hclA] at h
    exact h.symm
  have hnBc : IsClosed (Neg.neg '' B) :=
    ((Homeomorph.neg UnitThreeSphere).isClosedMap _ hBc.isClosed)
  have hniB : interior (Neg.neg '' B) = Neg.neg '' A := by
    have h : Neg.neg '' interior B = interior (Neg.neg '' B) :=
      (Homeomorph.neg UnitThreeSphere).image_interior B
    rw [hiB] at h
    exact h.symm
  have hiK : interior (antipodalBallComplement b) = (B ∪ Neg.neg '' B)ᶜ := by
    rw [antipodalBallComplement, interior_compl, closure_union, hclA, hnclA]
  have hregular : closure (interior (antipodalBallComplement b)) = antipodalBallComplement b := by
    rw [hiK, closure_compl, interior_union_of_disjoint_closure
      (by simpa only [hBc.isClosed.closure_eq, hnBc.closure_eq] using hBB), hiB, hniB]
    rfl
  refine ⟨hK.isCompact, hiK, hregular, ?_⟩
  rw [hK.frontier_eq, hiK, ← hfB, hBc.isClosed.frontier_eq, hiB]
  have hAB : A ⊆ B := image_mono Metric.ball_subset_closedBall
  ext x
  simp only [antipodalBallComplement, Set.mem_sdiff, mem_compl_iff, mem_union,
    mem_neg_image]
  have hdis (hx : x ∈ B) (hnx : -x ∈ B) : False :=
    disjoint_left.mp hBB hx ((mem_neg_image B x).mpr hnx)
  have hdis' (hx : x ∈ A) (hnx : -x ∈ B) : False := hdis (hAB hx) hnx
  have hdis'' (hx : x ∈ B) (hnx : -x ∈ A) : False := hdis hx (hAB hnx)
  change (¬(x ∈ A ∨ -x ∈ A) ∧ ¬¬(x ∈ B ∨ -x ∈ B)) ↔
    (x ∈ B ∧ x ∉ A) ∨ (-x ∈ B ∧ -x ∉ A)
  tauto

section ProjectedTopology

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
  {p : RealProjectiveThree} {U : Set M}
  (S : StandardPuncturedProjectiveCover M p U)

theorem image_topology_of_compact_antipodal
    {K : Set UnitThreeSphere} (hK : IsCompact K)
    (hp : ∀ x ∈ K, Quotient.mk' x ≠ p)
    (hneg : ∀ x, -x ∈ K ↔ x ∈ K)
    (hregular : closure (interior K) = K) :
    IsCompact (S.cover '' K) ∧
    interior (S.cover '' K) = S.cover '' interior K ∧
    closure (interior (S.cover '' K)) = S.cover '' K ∧
    frontier (S.cover '' K) = S.cover '' frontier K ∧
    (∀ x, Quotient.mk' x ≠ p → (S.cover x ∈ S.cover '' K ↔ x ∈ K)) ∧
    (∀ x, Quotient.mk' x ≠ p →
      (S.cover x ∈ interior (S.cover '' K) ↔ x ∈ interior K)) := by
  have hSc : ContinuousOn S.cover K := S.local_diffeomorph.contMDiffOn.continuousOn.mono hp
  have hTc : IsCompact (S.cover '' K) := hK.image_of_continuousOn hSc
  have hmem (x : UnitThreeSphere) (hxp : Quotient.mk' x ≠ p) :
      S.cover x ∈ S.cover '' K ↔ x ∈ K := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      rcases (S.fibers y x (hp y hy) hxp).mp hyx with h | h
      · exact h ▸ hy
      · exact (hneg x).mp (h ▸ hy)
    · exact mem_image_of_mem S.cover
  let v : PuncturedProjectiveSphere p → UnitThreeSphere := Subtype.val
  let f : PuncturedProjectiveSphere p → M := fun x => S.cover x
  have hv : IsLocalHomeomorph v :=
    (isOpen_puncturedProjectiveSphere p).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hf : IsLocalHomeomorph f :=
    S.isOpen_target.isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp
      S.restrictedCover_isLocalHomeomorph
  have hpre : f ⁻¹' (S.cover '' K) = v ⁻¹' K := by
    ext x
    exact hmem x x.property
  have hipre : f ⁻¹' interior (S.cover '' K) = v ⁻¹' interior K := by
    rw [hf.isOpenMap.preimage_interior_eq_interior_preimage hf.continuous, hpre,
      ← hv.isOpenMap.preimage_interior_eq_interior_preimage hv.continuous]
  have hi (x : UnitThreeSphere) (hxp : Quotient.mk' x ≠ p) :
      S.cover x ∈ interior (S.cover '' K) ↔ x ∈ interior K :=
    Set.ext_iff.mp hipre (⟨x, hxp⟩ : PuncturedProjectiveSphere p)
  have hiimage : interior (S.cover '' K) = S.cover '' interior K := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := interior_subset hy
      exact ⟨x, (hi x (hp x hx)).mp hy, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (hi x (hp x (interior_subset hx))).mpr hx
  have hTregular : closure (interior (S.cover '' K)) = S.cover '' K := by
    apply Subset.antisymm hTc.isClosed.closure_interior_subset
    rw [hiimage]
    have h := (hregular.symm ▸ hSc).image_closure
    simpa only [hregular] using h
  have hfront : frontier (S.cover '' K) = S.cover '' frontier K := by
    have hfpre : f ⁻¹' frontier (S.cover '' K) = v ⁻¹' frontier K := by
      rw [hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.continuous, hpre,
        ← hv.isOpenMap.preimage_frontier_eq_frontier_preimage hv.continuous]
    apply Subset.antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hTc.isClosed.frontier_subset hy
      exact ⟨x, (Set.ext_iff.mp hfpre (⟨x, hp x hx⟩ : PuncturedProjectiveSphere p)).mp hy, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact (Set.ext_iff.mp hfpre
        (⟨x, hp x (hK.isClosed.frontier_subset hx)⟩ : PuncturedProjectiveSphere p)).mpr hx
  exact ⟨hTc, hiimage, hTregular, hfront, hmem, hi⟩

theorem projectiveBallComplement_topology
    (a : UnitThreeSphere) (ha : Quotient.mk' a = p)
    (b : OpenPartialHomeomorph E3 UnitThreeSphere)
    (hbs : Metric.closedBall 0 1 ⊆ b.source) (hb0 : b 0 = a)
    (hBB : Disjoint (b '' Metric.closedBall 0 1)
      (Neg.neg '' (b '' Metric.closedBall 0 1))) :
    IsCompact (S.cover '' antipodalBallComplement b) ∧
    interior (S.cover '' antipodalBallComplement b) =
      S.cover '' (b '' Metric.closedBall 0 1 ∪ Neg.neg '' (b '' Metric.closedBall 0 1))ᶜ ∧
    closure (interior (S.cover '' antipodalBallComplement b)) =
      S.cover '' antipodalBallComplement b ∧
    frontier (S.cover '' antipodalBallComplement b) = S.cover '' (b '' Metric.sphere 0 1) ∧
    (∀ x, Quotient.mk' x ≠ p →
      (S.cover x ∈ S.cover '' antipodalBallComplement b ↔ x ∈ antipodalBallComplement b)) ∧
    (∀ x, Quotient.mk' x ≠ p →
      (S.cover x ∈ interior (S.cover '' antipodalBallComplement b) ↔
        x ∈ (b '' Metric.closedBall 0 1 ∪ Neg.neg '' (b '' Metric.closedBall 0 1))ᶜ)) := by
  obtain ⟨hK, hiK, hregular, hfK⟩ := antipodalBallComplement_topology b hbs hBB
  have hp {x : UnitThreeSphere} (hx : x ∈ antipodalBallComplement b) : Quotient.mk' x ≠ p :=
    antipodalBallComplement_avoids_puncture a ha b hb0 hx
  obtain ⟨hT, hiT, hregT, hfT, hmem, hi⟩ :=
    image_topology_of_compact_antipodal S hK (fun _ hx => hp hx)
      (neg_mem_antipodalBallComplement b) hregular
  have hboundary : S.cover '' (Neg.neg '' (b '' Metric.sphere 0 1)) =
      S.cover '' (b '' Metric.sphere 0 1) := by
    have hsp : b '' Metric.sphere 0 1 ⊆ antipodalBallComplement b :=
      (show b '' Metric.sphere 0 1 ⊆ frontier (antipodalBallComplement b) from
        fun _ hx => hfK.symm.subset (Or.inl hx)).trans hK.isClosed.frontier_subset
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (S.fibers x (-x) (hp (hsp hx))
        (hp ((neg_mem_antipodalBallComplement b x).mpr (hsp hx)))).mpr
          (Or.inr (neg_neg x).symm)⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨-x, mem_image_of_mem Neg.neg hx,
        (S.fibers (-x) x (hp ((neg_mem_antipodalBallComplement b x).mpr (hsp hx)))
          (hp (hsp hx))).mpr (Or.inr rfl)⟩
  refine ⟨hT, ?_, hregT, ?_, hmem, ?_⟩
  · rw [hiT, hiK]
  · rw [hfT, hfK, image_union, hboundary, union_self]
  · intro x hxp
    rw [← hiK]
    exact hi x hxp

theorem exists_projectiveBallComplement_collar
    (a : UnitThreeSphere) (ha : Quotient.mk' a = p)
    (b : OpenPartialHomeomorph E3 UnitThreeSphere)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    (hb0 : b 0 = a) {δ : ℝ} (hδ : 0 < δ)
    (hbs : Metric.ball 0 (Real.exp δ) ⊆ b.source)
    (hBB : Disjoint (b '' Metric.ball 0 (Real.exp δ))
      (Neg.neg '' (b '' Metric.ball 0 (Real.exp δ)))) :
    ∃ c : OpenPartialHomeomorph RoundCylinderSpace M,
      c.source = univ ×ˢ Ioo (-δ) δ ∧
      ContMDiffOn CylModel (𝓡 3) ∞ c c.source ∧
      ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target ∧
      (∀ z ∈ c.source, c z = S.cover (b (Real.exp z.2 • (z.1 : E3)))) ∧
      frontier (S.cover '' antipodalBallComplement b) =
        range (fun q : UnitTwoSphere => c (q, 0)) ∧
      (∀ y ∈ c.target, y ∈ S.cover '' antipodalBallComplement b ↔ 0 ≤ (c.symm y).2) ∧
      (∀ y ∈ c.target,
        y ∈ interior (S.cover '' antipodalBallComplement b) ↔ 0 < (c.symm y).2) ∧
      c.target ⊆ U := by
  let : Nonempty RoundCylinderSpace := ⟨(Poincare.Topology.standardSpherePole 0, 0)⟩
  let R := Metric.ball (0 : E3) (Real.exp δ)
  let V : Opens RoundCylinderSpace :=
    ⟨univ ×ˢ Ioo (-δ) δ, isOpen_univ.prod isOpen_Ioo⟩
  let radial : RoundCylinderSpace → E3 := fun z => Real.exp z.2 • (z.1 : E3)
  have hrad (z : RoundCylinderSpace) : ‖radial z‖ = Real.exp z.2 := by
    simp [radial, norm_smul, Real.norm_eq_abs, Real.abs_exp]
  have hradR (z : RoundCylinderSpace) (hz : z ∈ V) : radial z ∈ R := by
    rw [Metric.mem_ball, dist_zero_right, hrad]
    exact Real.exp_lt_exp.mpr hz.2.2
  have hsmall : Metric.closedBall (0 : E3) 1 ⊆ R :=
    Metric.closedBall_subset_ball (Real.one_lt_exp_iff.mpr hδ)
  have hsmallS : Metric.closedBall (0 : E3) 1 ⊆ b.source := hsmall.trans hbs
  have hsmallB : Disjoint (b '' Metric.closedBall 0 1)
      (Neg.neg '' (b '' Metric.closedBall 0 1)) :=
    hBB.mono (image_mono hsmall) (image_mono (image_mono hsmall))
  have hp (z : RoundCylinderSpace) (hz : z ∈ V) : Quotient.mk' (b (radial z)) ≠ p := by
    intro hzp
    rcases Quotient.exact (hzp.trans ha.symm) with h | h
    · have heq : radial z = 0 := b.injOn (hbs (hradR z hz)) (hsmallS (by simp)) (h.trans hb0.symm)
      exact smul_ne_zero (Real.exp_ne_zero _) (ne_zero_of_mem_unit_sphere z.1) heq
    · have haR : a ∈ b '' R := hb0 ▸ mem_image_of_mem b (hsmall (by simp))
      exact disjoint_left.mp hBB (mem_image_of_mem b (hradR z hz)) ⟨a, haR, h.symm⟩
  let f : RoundCylinderSpace → M := fun z => S.cover (b (radial z))
  have hradinj : Function.Injective radial := by
    intro z w hzw
    apply Poincare.sphereCylinderDiffeomorphPunctured.injective
    exact Subtype.ext hzw
  have hinj : InjOn f V := by
    intro z hz w hw hzw
    rcases (S.fibers _ _ (hp z hz) (hp w hw)).mp hzw with h | h
    · exact hradinj (b.injOn (hbs (hradR z hz)) (hbs (hradR w hw)) h)
    · exact False.elim (disjoint_left.mp hBB (mem_image_of_mem b (hradR z hz))
        ⟨b (radial w), mem_image_of_mem b (hradR w hw), h.symm⟩)
  have hradloc : IsLocalDiffeomorph CylModel (𝓡 3) ∞ radial := by
    intro z
    exact (Poincare.sphereCylinderDiffeomorphPunctured.isLocalDiffeomorph z).comp
      (𝓡 3) E3 (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3)
        Poincare.puncturedThreeSpace (Poincare.sphereCylinderDiffeomorphPunctured z))
  let B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 UnitThreeSphere ∞ := {
    toPartialEquiv := b.toPartialEquiv
    open_source := b.open_source
    open_target := b.open_target
    contMDiffOn_toFun := hb
    contMDiffOn_invFun := hbi }
  have hloc (z : RoundCylinderSpace) (hz : z ∈ V) :
      IsLocalDiffeomorphAt CylModel (𝓡 3) ∞ f z := by
    have hbloc : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ b (radial z) :=
      ⟨B, hbs (hradR z hz), fun _ _ => rfl⟩
    exact (hradloc z).comp (𝓡 3) M
      (hbloc.comp (𝓡 3) M (S.local_diffeomorph ⟨b (radial z), hp z hz⟩))
  have hVloc : IsLocalDiffeomorph CylModel (𝓡 3) ∞ (fun z : V => f z) := by
    intro z
    exact (Poincare.isLocalDiffeomorph_opensSubtypeVal CylModel V z).comp (𝓡 3) M
      (hloc z z.property)
  let e : OpenPartialHomeomorph RoundCylinderSpace M :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict (hinj.toPartialEquiv f V)
      (fun z hz => (hloc z hz).contMDiffAt.continuousAt.continuousWithinAt)
      hVloc.isOpenMap V.isOpen
  have hes : e.source = univ ×ˢ Ioo (-δ) δ := rfl
  have heq (z : RoundCylinderSpace) : e z = S.cover (b (radial z)) := rfl
  have he : ContMDiffOn CylModel (𝓡 3) ∞ e e.source :=
    fun z hz => (hloc z hz).contMDiffAt.contMDiffWithinAt
  have hei : ContMDiffOn (𝓡 3) CylModel ∞ e.symm e.target := by
    intro y hy
    let z := e.symm y
    have hz : z ∈ V := e.map_target hy
    have hf := hloc z hz
    have hfy : f z = y := e.right_inv hy
    have hgerm : e.symm =ᶠ[𝓝 y] hf.localInverse := by
      have hc : ContinuousAt e.symm y := e.continuousAt_symm hy
      filter_upwards [e.open_target.mem_nhds hy,
        hc.preimage_mem_nhds (hf.localInverse.open_target.mem_nhds
          hf.localInverse_mem_target)] with x hx hxin
      exact (hf.localInverse_left_inv hxin).symm.trans
        (congrArg hf.localInverse (e.right_inv hx))
    have hi : ContMDiffAt (𝓡 3) CylModel ∞ hf.localInverse y := by
      rw [← hfy]
      exact hf.localInverse_contMDiffAt
    exact (hi.congr_of_eventuallyEq hgerm).contMDiffWithinAt
  obtain ⟨_, _, _, hfront, hmem, hinterior⟩ :=
    projectiveBallComplement_topology S a ha b hsmallS hb0 hsmallB
  have hnotneg (z : RoundCylinderSpace) (hz : z ∈ V) :
      -b (radial z) ∉ b '' Metric.closedBall 0 1 := by
    intro h
    exact disjoint_left.mp hBB (mem_image_of_mem b (hradR z hz))
      ((mem_neg_image (b '' R) (b (radial z))).mpr (image_mono hsmall h))
  have hballmem (z : RoundCylinderSpace) (hz : z ∈ V) :
      b (radial z) ∈ b '' Metric.ball 0 1 ↔ z.2 < 0 := by
    constructor
    · rintro ⟨w, hw, heq⟩
      have hwr := b.injOn (hsmallS (Metric.ball_subset_closedBall hw)) (hbs (hradR z hz)) heq
      have hn := mem_ball_zero_iff.mp (hwr ▸ hw)
      rw [hrad] at hn
      exact Real.exp_lt_one_iff.mp hn
    · intro hz0
      exact mem_image_of_mem b (by rw [mem_ball_zero_iff, hrad]; exact Real.exp_lt_one_iff.mpr hz0)
  have hclosedmem (z : RoundCylinderSpace) (hz : z ∈ V) :
      b (radial z) ∈ b '' Metric.closedBall 0 1 ↔ z.2 ≤ 0 := by
    constructor
    · rintro ⟨w, hw, heq⟩
      have hwr := b.injOn (hsmallS hw) (hbs (hradR z hz)) heq
      have hn := mem_closedBall_zero_iff.mp (hwr ▸ hw)
      rw [hrad] at hn
      exact Real.exp_le_one_iff.mp hn
    · intro hz0
      exact mem_image_of_mem b (by rw [mem_closedBall_zero_iff, hrad]; exact Real.exp_le_one_iff.mpr hz0)
  have hside (z : RoundCylinderSpace) (hz : z ∈ V) :
      e z ∈ S.cover '' antipodalBallComplement b ↔ 0 ≤ z.2 := by
    rw [heq, hmem _ (hp z hz), mem_antipodalBallComplement, hballmem z hz]
    have hn : -b (radial z) ∉ b '' Metric.ball 0 1 :=
      fun h => hnotneg z hz (image_mono Metric.ball_subset_closedBall h)
    simp only [hn, not_false_eq_true, and_true, not_lt]
  have hiside (z : RoundCylinderSpace) (hz : z ∈ V) :
      e z ∈ interior (S.cover '' antipodalBallComplement b) ↔ 0 < z.2 := by
    rw [heq, hinterior _ (hp z hz)]
    simp only [mem_compl_iff, mem_union, mem_neg_image, hclosedmem z hz, hnotneg z hz,
      or_false, not_le]
  refine ⟨e, hes, he, hei, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · rw [hfront]
    ext y
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨⟨z, hz⟩, by simp [heq, radial]⟩
    · rintro ⟨q, rfl⟩
      exact ⟨b q, mem_image_of_mem b q.property, by simp [heq, radial]⟩
  · intro y hy
    have h := hside (e.symm y) (e.map_target hy)
    rwa [e.right_inv hy] at h
  · intro y hy
    have h := hiside (e.symm y) (e.map_target hy)
    rwa [e.right_inv hy] at h
  · intro y hy
    have h := S.image_eq.subset (mem_image_of_mem S.cover (hp (e.symm y) (e.map_target hy)))
    change e (e.symm y) ∈ U at h
    rwa [e.right_inv hy] at h

end ProjectedTopology

end PoincareConjecture.ProjectiveGluing
