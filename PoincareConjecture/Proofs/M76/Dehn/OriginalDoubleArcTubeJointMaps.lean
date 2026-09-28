import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeJointQuarters
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedGraph
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedBallExtension
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLDiskModel
import PoincareConjecture.Proofs.M76.Mathlib.TriangleDiskRegions
import PoincareConjecture.Proofs.M76.Mathlib.PolygonTriangleRegion
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCutArcIntervals











set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)



def signedTubeCorner (i : Fin 2) (sign : Bool) : P2 :=
  if i = 0 then (0, if sign then 1 else -1)
  else (if sign then 1 else -1, 0)


def signedTubeRadius (i : Fin 2) (sign : Bool) : Set P2 :=
  segment ℝ (0, 0) (signedTubeCorner i sign)


def signedTubeOuterArc (eps delta : Bool) : Set P2 :=
  segment ℝ (signedTubeCorner 1 eps) (signedTubeCorner 0 delta)


def signedTubeQuarter (eps delta : Bool) : Set P2 :=
  convexHull ℝ (range ![(0, 0), signedTubeCorner 1 eps,
    signedTubeCorner 0 delta])


def signedTubeDiamond : Set P2 :=
  ⋃ eps : Bool, ⋃ delta : Bool, signedTubeQuarter eps delta


def signedTubeRadialRim (eps delta : Bool) : Set P2 :=
  signedTubeRadius 0 delta ∪ signedTubeRadius 1 eps


def signedTubeSheet (i : Fin 2) : Set P2 :=
  signedTubeRadius i false ∪ signedTubeRadius i true

theorem signedTube_corner_ne_center (i : Fin 2) (sign : Bool) :
    signedTubeCorner i sign ≠ (0, 0) := by
  fin_cases i <;> cases sign <;>
    norm_num [signedTubeCorner, Fin.cases_zero, Fin.cases_succ]

theorem signedTube_corner_ne_corner (i : Fin 2) (sign : Bool)
    (j : Fin 2) (other : Bool) (h : (i, sign) ≠ (j, other)) :
    signedTubeCorner i sign ≠ signedTubeCorner j other := by
  fin_cases i <;> fin_cases j <;> cases sign <;> cases other <;>
    simp_all [signedTubeCorner] <;> norm_num

theorem signedTube_radius_ball (i : Fin 2) (sign : Bool) :
    IsFinitePLBallPair ℝ (signedTubeRadius i sign)
      {(0, 0), signedTubeCorner i sign} := by
  have h := (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)).affine_image
    (ContinuousAffineMap.lineMap (0 : P2) (signedTubeCorner i sign))
    (AffineMap.lineMap_injective ℝ (signedTube_corner_ne_center i sign).symm).injOn
  change IsFinitePLBallPair ℝ
      ((AffineMap.lineMap (0 : P2) (signedTubeCorner i sign)) '' Icc (0 : ℝ) 1)
      ((AffineMap.lineMap (0 : P2) (signedTubeCorner i sign)) '' ({0, 1} : Set ℝ)) at h
  rw [← segment_eq_image_lineMap, image_pair, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] at h
  exact h

theorem signedTube_segment_ball (a b : P2) (hab : a ≠ b) :
    IsFinitePLBallPair ℝ (segment ℝ a b) {a, b} := by
  have h := (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)).affine_image
    (ContinuousAffineMap.lineMap a b)
    (AffineMap.lineMap_injective ℝ hab).injOn
  change IsFinitePLBallPair ℝ
      ((AffineMap.lineMap a b) '' Icc (0 : ℝ) 1)
      ((AffineMap.lineMap a b) '' ({0, 1} : Set ℝ)) at h
  rw [← segment_eq_image_lineMap, image_pair, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] at h
  exact h

private theorem signedTube_radius_inter_false (i : Fin 2) :
    signedTubeRadius i false ∩ signedTubeRadius i true = {(0, 0)} := by
  fin_cases i
  · apply Subset.antisymm
    · intro z hz
      rcases hz.1 with ⟨u, v, hu, hv, huv, hzu⟩
      rcases hz.2 with ⟨u', v', hu', hv', huv', hzv⟩
      norm_num [signedTubeCorner, signedTubeRadius, Fin.cases_zero,
        Fin.cases_succ] at hzu hzv ⊢
      have h : -v = v' := by
        exact congrArg Prod.snd (hzu.trans hzv.symm)
      have hv0 : v = 0 := by linarith
      have hv'0 : v' = 0 := by linarith
      rw [← hzu]
      simp [hv0, hv'0]
    · rintro z rfl
      exact ⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩
  · apply Subset.antisymm
    · intro z hz
      rcases hz.1 with ⟨u, v, hu, hv, huv, hzu⟩
      rcases hz.2 with ⟨u', v', hu', hv', huv', hzv⟩
      norm_num [signedTubeCorner, signedTubeRadius, Fin.cases_zero,
        Fin.cases_succ] at hzu hzv ⊢
      have h : -v = v' := by
        exact congrArg Prod.fst (hzu.trans hzv.symm)
      have hv0 : v = 0 := by linarith
      have hv'0 : v' = 0 := by linarith
      rw [← hzu]
      simp [hv0, hv'0]
    · rintro z rfl
      exact ⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

theorem signedTube_radius_inter (i : Fin 2) (sign : Bool) :
    signedTubeRadius i sign ∩ signedTubeRadius i (!sign) = {(0, 0)} := by
  cases sign
  · exact signedTube_radius_inter_false i
  · simpa [inter_comm] using signedTube_radius_inter_false i

theorem signedTube_cross_radius_inter (eps delta : Bool) :
    signedTubeRadius 0 delta ∩ signedTubeRadius 1 eps = {(0, 0)} := by
  apply Subset.antisymm
  · intro z hz
    rcases hz.1 with ⟨u, v, hu, hv, huv, hzu⟩
    rcases hz.2 with ⟨u', v', hu', hv', huv', hzv⟩
    fin_cases eps <;> fin_cases delta <;>
      norm_num [signedTubeCorner, Fin.cases_zero, Fin.cases_succ] at hzu hzv ⊢
    all_goals
      have hxy := hzu.trans hzv.symm
      have hf := congrArg Prod.fst hxy
      have hs := congrArg Prod.snd hxy
      rw [← hzu]
      apply Prod.ext <;> norm_num at hf hs ⊢ <;> linarith [hu, hv, hu', hv']
  · rintro z rfl
    exact ⟨left_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

theorem signedTube_quarter_ball (eps delta : Bool) :
    IsFinitePLBallPair P2 (signedTubeQuarter eps delta)
      (signedTubeOuterArc eps delta ∪ signedTubeRadialRim eps delta) := by
  let P : Polygon P2 3 :=
    ⟨![(0, 0), signedTubeCorner 1 eps, signedTubeCorner 0 delta]⟩
  have hP : AffineIndependent ℝ P := by
    let S : AffineSubspace ℝ P2 :=
      (affineSpan ℝ {(0 : ℝ)}).comap (LinearMap.snd ℝ ℝ ℝ).toAffineMap
    have h : AffineIndependent ℝ
        ![(signedTubeCorner 1 eps), (signedTubeCorner 0 delta), (0, 0)] := by
      apply affineIndependent_of_ne_of_mem_of_notMem_of_mem (s := S)
      · fin_cases eps <;> fin_cases delta <;>
          norm_num [signedTubeCorner, Fin.cases_zero, Fin.cases_succ]
      · simp [S, signedTubeCorner, Fin.cases_zero, Fin.cases_succ]
      · cases delta <;> norm_num [S, signedTubeCorner]
      · simp [S, signedTubeCorner, Fin.cases_zero, Fin.cases_succ]
    simpa [P] using h.comm_right.comm_left
  have hball := P.isFinitePLBallPair_convexHull_triangle hP
  have hboundary : P.boundary ℝ =
      signedTubeOuterArc eps delta ∪ signedTubeRadialRim eps delta := by
    ext z
    simp only [Polygon.boundary, Polygon.edgeSet, affineSegment_eq_segment,
      mem_iUnion, mem_union]
    fin_cases eps <;> fin_cases delta <;>
      simp [P, signedTubeOuterArc, signedTubeRadialRim, signedTubeRadius,
        signedTubeCorner, Fin.cases_zero, Fin.cases_succ, Fin.exists_fin_succ,
        segment_symm, or_assoc, or_left_comm, or_comm]
  rw [P.frontier_convexHull_triangle hP, hboundary] at hball
  simpa only [signedTubeQuarter, P] using hball

theorem signedTube_center_mem :
    (0, 0) ∈ signedTubeQuarter false false := by
  apply subset_convexHull ℝ
  simp [signedTubeQuarter, signedTubeCorner]


private def jointSign (b : Bool) : ℝ := if b then 1 else -1

private theorem signedTube_quarter_mem_iff (eps delta : Bool) (x : P2) :
    x ∈ signedTubeQuarter eps delta ↔
      0 ≤ jointSign eps * x.1 ∧ 0 ≤ jointSign delta * x.2 ∧
        jointSign eps * x.1 + jointSign delta * x.2 ≤ 1 := by
  let P : Fin 3 → P2 := ![(0, 0), signedTubeCorner 1 eps, signedTubeCorner 0 delta]
  let L : P2 →ₗ[ℝ] ℝ := jointSign eps • LinearMap.fst ℝ ℝ ℝ
  let M : P2 →ₗ[ℝ] ℝ := jointSign delta • LinearMap.snd ℝ ℝ ℝ
  have hL : convexHull ℝ (range P) ⊆ {x | 0 ≤ L x} := by
    apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      fin_cases i <;> cases eps <;> cases delta <;>
        norm_num [P, L, jointSign, signedTubeCorner]
    · exact (convex_Ici (0 : ℝ)).linear_preimage L
  have hM : convexHull ℝ (range P) ⊆ {x | 0 ≤ M x} := by
    apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      fin_cases i <;> cases eps <;> cases delta <;>
        norm_num [P, M, jointSign, signedTubeCorner]
    · exact (convex_Ici (0 : ℝ)).linear_preimage M
  have hLM : convexHull ℝ (range P) ⊆ {x | (L + M) x ≤ 1} := by
    apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      fin_cases i <;> cases eps <;> cases delta <;>
        norm_num [P, L, M, jointSign, signedTubeCorner]
    · exact (convex_Iic (1 : ℝ)).linear_preimage (L + M)
  constructor
  · intro hx
    exact ⟨hL hx, hM hx, hLM hx⟩
  · rintro ⟨hx, hy, hsum⟩
    apply mem_convexHull_of_exists_fintype
      ![1 - jointSign eps * x.1 - jointSign delta * x.2,
        jointSign eps * x.1, jointSign delta * x.2] P
    · intro i
      fin_cases i <;> dsimp <;> linarith
    · simp [Fin.sum_univ_succ]
    · exact mem_range_self
    · cases eps <;> cases delta <;>
        apply Prod.ext <;> simp [P, Fin.sum_univ_succ, jointSign, signedTubeCorner]

private theorem signedTube_radius_zero_mem_iff (sign : Bool) (x : P2) :
    x ∈ signedTubeRadius 0 sign ↔
      x.1 = 0 ∧ 0 ≤ jointSign sign * x.2 ∧ jointSign sign * x.2 ≤ 1 := by
  constructor
  · rintro ⟨u, v, hu, hv, huv, heq⟩
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    cases sign <;> simp [signedTubeCorner, jointSign] at hx hy ⊢ <;>
      exact ⟨hx.symm, by linarith, by linarith⟩
  · rintro ⟨hx, hy, hy1⟩
    refine ⟨1 - jointSign sign * x.2, jointSign sign * x.2,
      by linarith, hy, by ring, ?_⟩
    cases sign <;> apply Prod.ext <;> simp [signedTubeCorner, jointSign, hx]

private theorem signedTube_radius_one_mem_iff (sign : Bool) (x : P2) :
    x ∈ signedTubeRadius 1 sign ↔
      x.2 = 0 ∧ 0 ≤ jointSign sign * x.1 ∧ jointSign sign * x.1 ≤ 1 := by
  constructor
  · rintro ⟨u, v, hu, hv, huv, heq⟩
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    cases sign <;> simp [signedTubeCorner, jointSign] at hx hy ⊢ <;>
      exact ⟨hy.symm, by linarith, by linarith⟩
  · rintro ⟨hy, hx, hx1⟩
    refine ⟨1 - jointSign sign * x.1, jointSign sign * x.1,
      by linarith, hx, by ring, ?_⟩
    cases sign <;> apply Prod.ext <;> simp [signedTubeCorner, jointSign, hy]

private theorem signedTube_outer_mem_iff (eps delta : Bool) (x : P2) :
    x ∈ signedTubeOuterArc eps delta ↔
      0 ≤ jointSign eps * x.1 ∧ 0 ≤ jointSign delta * x.2 ∧
        jointSign eps * x.1 + jointSign delta * x.2 = 1 := by
  constructor
  · rintro ⟨u, v, hu, hv, huv, heq⟩
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    cases eps <;> cases delta <;>
      simp [signedTubeCorner, jointSign] at hx hy ⊢ <;>
      exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hx, hy, hsum⟩
    refine ⟨jointSign eps * x.1, jointSign delta * x.2, hx, hy, hsum, ?_⟩
    cases eps <;> cases delta <;>
      apply Prod.ext <;> simp [signedTubeCorner, jointSign]

theorem signedTube_outer_inter_rim (eps delta : Bool) :
    signedTubeOuterArc eps delta ∩ signedTubeRadialRim eps delta =
      {signedTubeCorner 0 delta, signedTubeCorner 1 eps} := by
  ext x
  simp only [mem_inter_iff, signedTubeRadialRim, mem_union,
    signedTube_outer_mem_iff, signedTube_radius_zero_mem_iff,
    signedTube_radius_one_mem_iff, mem_insert_iff, mem_singleton_iff]
  cases eps <;> cases delta <;>
    simp [jointSign, signedTubeCorner, Prod.ext_iff] <;>
    constructor
  all_goals
    first
    | rintro ⟨h, h' | h'⟩ <;> rcases h with ⟨h1, h2, h3⟩ <;>
        rcases h' with ⟨h4, h5, h6⟩ <;> simp_all <;> linarith
    | rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> simp_all

theorem signedTube_quarter_inter_delta (eps delta : Bool) :
    signedTubeQuarter eps delta ∩ signedTubeQuarter eps (!delta) =
      signedTubeRadius 1 eps := by
  ext x
  simp only [mem_inter_iff, signedTube_quarter_mem_iff,
    signedTube_radius_one_mem_iff]
  cases eps <;> cases delta <;> simp [jointSign] <;>
    constructor
  all_goals
    first
    | rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩; exact ⟨by linarith, by linarith, by linarith⟩
    | rintro ⟨h1, h2, h3⟩; simp_all <;> linarith

theorem signedTube_quarter_inter_eps (eps delta : Bool) :
    signedTubeQuarter eps delta ∩ signedTubeQuarter (!eps) delta =
      signedTubeRadius 0 delta := by
  ext x
  simp only [mem_inter_iff, signedTube_quarter_mem_iff,
    signedTube_radius_zero_mem_iff]
  cases eps <;> cases delta <;> simp [jointSign] <;>
    constructor
  all_goals
    first
    | rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩; exact ⟨by linarith, by linarith, by linarith⟩
    | rintro ⟨h1, h2, h3⟩; simp_all <;> linarith

theorem signedTube_quarter_inter_opposite (eps delta : Bool) :
    signedTubeQuarter eps delta ∩ signedTubeQuarter (!eps) (!delta) = {(0, 0)} := by
  ext x
  simp only [mem_inter_iff, signedTube_quarter_mem_iff, mem_singleton_iff,
    Prod.ext_iff]
  cases eps <;> cases delta <;> simp [jointSign] <;>
    constructor
  all_goals
    first
    | rintro ⟨⟨h1, h2, h3⟩, h4, h5, h6⟩; exact ⟨by linarith, by linarith⟩
    | rintro ⟨h1, h2⟩; simp_all

private theorem signedTube_quarter_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (m : E) (a : Fin 2 → Bool → E) (Q : Bool → Bool → Set E) (q : Set E)
    (eps delta : Bool)
    (hQB : IsFinitePLBallPair P2 (Q eps delta)
      ((Q eps delta ∩ q) ∪ (segment ℝ m (a 0 delta) ∪ segment ℝ m (a 1 eps))))
    (hOB : IsFinitePLBallPair ℝ (Q eps delta ∩ q) {a 0 delta, a 1 eps})
    (hUO : (segment ℝ m (a 0 delta) ∪ segment ℝ m (a 1 eps)) ∩
      (Q eps delta ∩ q) = {a 0 delta, a 1 eps})
    (hCross : segment ℝ m (a 0 delta) ∩ segment ℝ m (a 1 eps) = {m})
    (e : ∀ i sign, signedTubeRadius i sign ≃ₜ segment ℝ m (a i sign))
    (he : ∀ i sign, (e i sign).IsFinitePL)
    (heCenter : ∀ i sign (x : signedTubeRadius i sign),
      (e i sign x : E) = m ↔ (x : P2) = (0, 0))
    (heEnd : ∀ i sign (x : signedTubeRadius i sign),
      (e i sign x : E) = a i sign ↔ (x : P2) = signedTubeCorner i sign) :
    ∃ f : signedTubeQuarter eps delta ≃ₜ Q eps delta, f.IsFinitePL ∧
      (∀ x : signedTubeRadius 0 delta,
        (f ⟨x, (signedTube_quarter_ball eps delta).1 (Or.inr (Or.inl x.property))⟩ : E) =
          e 0 delta x) ∧
      (∀ x : signedTubeRadius 1 eps,
        (f ⟨x, (signedTube_quarter_ball eps delta).1 (Or.inr (Or.inr x.property))⟩ : E) =
          e 1 eps x) := by
  have hSource := signedTube_cross_radius_inter eps delta
  have hoverlap (x : signedTubeRadius 0 delta) :
      (x : P2) ∈ signedTubeRadius 1 eps ↔ (e 0 delta x : E) ∈ segment ℝ m (a 1 eps) := by
    have hs : (x : P2) ∈ signedTubeRadius 1 eps ↔ (x : P2) = (0, 0) := by
      constructor
      · intro hx
        exact hSource.subset ⟨x.property, hx⟩
      · intro hx
        rw [hx]
        exact left_mem_segment ℝ _ _
    have ht : (e 0 delta x : E) ∈ segment ℝ m (a 1 eps) ↔ (e 0 delta x : E) = m := by
      constructor
      · intro hx
        exact hCross.subset ⟨(e 0 delta x).property, hx⟩
      · intro hx
        rw [hx]
        exact left_mem_segment ℝ _ _
    exact hs.trans ((heCenter 0 delta x).symm.trans ht.symm)
  have hagree (x : P2) (hx : x ∈ signedTubeRadius 0 delta)
      (hy : x ∈ signedTubeRadius 1 eps) :
      (e 0 delta ⟨x, hx⟩ : E) = e 1 eps ⟨x, hy⟩ := by
    have hzero : x = (0, 0) := hSource.subset ⟨hx, hy⟩
    exact ((heCenter 0 delta ⟨x, hx⟩).mpr hzero).trans
      ((heCenter 1 eps ⟨x, hy⟩).mpr hzero).symm
  obtain ⟨r, hr, hr0, hr1⟩ := Homeomorph.exists_union_finitePL
    (e 0 delta) (e 1 eps) (he 0 delta) (he 1 eps) hoverlap hagree
  have hEnd0 : signedTubeCorner 0 delta ∈ signedTubeRadialRim eps delta :=
    Or.inl (right_mem_segment ℝ _ _)
  have hEnd1 : signedTubeCorner 1 eps ∈ signedTubeRadialRim eps delta :=
    Or.inr (right_mem_segment ℝ _ _)
  have hrEnd0 : (r ⟨signedTubeCorner 0 delta, hEnd0⟩ : E) = a 0 delta :=
    (hr0 ⟨signedTubeCorner 0 delta, right_mem_segment ℝ _ _⟩).trans
      ((heEnd 0 delta ⟨signedTubeCorner 0 delta, right_mem_segment ℝ _ _⟩).mpr rfl)
  have hrEnd1 : (r ⟨signedTubeCorner 1 eps, hEnd1⟩ : E) = a 1 eps :=
    (hr1 ⟨signedTubeCorner 1 eps, right_mem_segment ℝ _ _⟩).trans
      ((heEnd 1 eps ⟨signedTubeCorner 1 eps, right_mem_segment ℝ _ _⟩).mpr rfl)
  have hrBoundary (x : signedTubeRadialRim eps delta) :
      (x : P2) ∈ ({signedTubeCorner 0 delta, signedTubeCorner 1 eps} : Set P2) ↔
        (r x : E) ∈ ({a 0 delta, a 1 eps} : Set E) := by
    have h0 : (r x : E) = a 0 delta ↔ (x : P2) = signedTubeCorner 0 delta := by
      constructor
      · intro h
        exact congrArg Subtype.val (r.injective (Subtype.ext (h.trans hrEnd0.symm)))
      · intro h
        exact (congrArg (fun y : signedTubeRadialRim eps delta => (r y : E))
          (show x = ⟨signedTubeCorner 0 delta, hEnd0⟩ from Subtype.ext h)).trans hrEnd0
    have h1 : (r x : E) = a 1 eps ↔ (x : P2) = signedTubeCorner 1 eps := by
      constructor
      · intro h
        exact congrArg Subtype.val (r.injective (Subtype.ext (h.trans hrEnd1.symm)))
      · intro h
        exact (congrArg (fun y : signedTubeRadialRim eps delta => (r y : E))
          (show x = ⟨signedTubeCorner 1 eps, hEnd1⟩ from Subtype.ext h)).trans hrEnd1
    simp only [mem_insert_iff, mem_singleton_iff, h0, h1]
  have hOuter : IsFinitePLBallPair ℝ (signedTubeOuterArc eps delta)
      {signedTubeCorner 0 delta, signedTubeCorner 1 eps} := by
    simpa only [signedTubeOuterArc, pair_comm] using signedTube_segment_ball
      (signedTubeCorner 1 eps) (signedTubeCorner 0 delta)
      (signedTube_corner_ne_corner 1 eps 0 delta (by simp))
  obtain ⟨f, hf, hfR, _, _⟩ := (signedTube_quarter_ball eps delta).exists_extension_of_boundary_piece
    hQB hOuter hOB (signedTube_outer_inter_rim eps delta)
    (by simpa only [inter_comm] using hUO) r hr hrBoundary
  refine ⟨f, hf, ?_, ?_⟩
  · intro x
    exact (congrArg Subtype.val (hfR ⟨x, Or.inl x.property⟩)).trans (hr0 x)
  · intro x
    exact (congrArg Subtype.val (hfR ⟨x, Or.inr x.property⟩)).trans (hr1 x)


theorem signedTubeRadius_subset_diamond (i : Fin 2) (sign : Bool) :
    signedTubeRadius i sign ⊆ signedTubeDiamond := by
  intro x hx
  fin_cases i
  · exact mem_iUnion.mpr ⟨false, mem_iUnion.mpr ⟨sign,
      (signedTube_quarter_ball false sign).1 (Or.inr (Or.inl hx))⟩⟩
  · exact mem_iUnion.mpr ⟨sign, mem_iUnion.mpr ⟨false,
      (signedTube_quarter_ball sign false).1 (Or.inr (Or.inr hx))⟩⟩

open Classical in





theorem exists_original_signed_tube_joint_boundary_maps
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R C A : Set X}
    (hAC : A ⊆ interior C) (hAR : A ⊆ R) (hAF : (A ∩ frontier R).Finite)
    (S : Fin 2 → Set X) (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (F : X → E) (hF : Continuous F) (H : C ≃ₜ K.space)
    (hH : ∀ x : C, (H x : E) = F x) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K)
    (hfull : ∀ i t, t ∈ K.faces → (∀ v ∈ t, v ∈ (M i).vertices) → t ∈ (M i).faces)
    (reg fr arc : κ) (sheet : Fin 2 → κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ (g z : X) ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ (g z : X) ∈ frontier R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ (g z : X) ∈ A)
    (hsheet : ∀ i z, z ∈ K.space →
      (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (B : (M arc).vertices → OpenPartialHomeomorph X V3)
    (hB : ∀ p : (M arc).vertices,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space (B p).source ∧
      (K.closedStar p).AffineOnFaces (fun z => B p (g z)) ∧
      (∀ y ∈ (B p).source, y ∈ A ↔ y ∈ R ∧ B p y 0 = 0 ∧ B p y 1 = 0) ∧
      ∀ i y, y ∈ (B p).source →
        (y ∈ S i ↔ y ∈ R ∧ B p y i.castSucc = 0))
    (s : Finset E) (hs : s ∈ (M arc).faces) (hcard : s.card = 2) :
    let J := K.barycentricDualBlock s
    let m := s.centroid ℝ id
    let q := (J.link m).space
    let I := fun i : Fin 2 => ((M (sheet i)).barycentricDualBlock s).space
    ∃ (p : (M arc).vertices) (T : Fin 2 → Bool → Finset E),
      let a := fun i sign => (T i sign).centroid ℝ id
      let rad := fun i sign => segment ℝ m (a i sign)
      let Q := fun eps delta : Bool => {z | z ∈ J.space ∧
        (if eps then 0 ≤ B p (g z) 0 else B p (g z) 0 ≤ 0) ∧
        if delta then 0 ≤ B p (g z) 1 else B p (g z) 1 ≤ 0}
      ∃ (H : signedTubeDiamond ≃ₜ J.space), H.IsFinitePL ∧
        (∀ eps delta (x : signedTubeQuarter eps delta),
          (H ⟨x, by exact mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, x.property⟩⟩⟩ : E) ∈
            Q eps delta) ∧
        (∀ eps delta (x : signedTubeQuarter eps delta),
          (x : P2) ∈ signedTubeQuarter eps delta ↔
            (H ⟨x, by exact mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, x.property⟩⟩⟩ : E) ∈
              Q eps delta) ∧
        (∀ (i : Fin 2) (x : signedTubeDiamond),
          (x : P2) ∈ signedTubeSheet i ↔
            (H x : E) ∈ I i) ∧
        (H ⟨(0, 0), by
          exact mem_iUnion.mpr ⟨false, mem_iUnion.mpr ⟨false,
            signedTube_center_mem⟩⟩⟩ : E) = m ∧
        (∀ eps delta, Q eps delta ∩ (M (sheet 0)).space =
          rad 0 delta) ∧
        (∀ eps delta, Q eps delta ∩ (M (sheet 1)).space =
          rad 1 eps) ∧
        (p : E) ∈ s ∧
        ∃ (quarter : ∀ eps delta, signedTubeQuarter eps delta ≃ₜ Q eps delta)
          (radius : ∀ i sign, signedTubeRadius i sign ≃ₜ rad i sign),
          (∀ eps delta, (quarter eps delta).IsFinitePL) ∧
          (∀ i sign, (radius i sign).IsFinitePL) ∧
          (∀ eps delta (x : signedTubeQuarter eps delta),
            (H ⟨x, mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, x.property⟩⟩⟩ : E) =
              quarter eps delta x) ∧
          (∀ i sign (x : signedTubeRadius i sign),
            (H ⟨x, signedTubeRadius_subset_diamond i sign x.property⟩ : E) = radius i sign x) ∧
          (∀ i sign (x : signedTubeRadius i sign),
            (radius i sign x : E) = m ↔ (x : P2) = (0, 0)) ∧
          (∀ i sign (x : signedTubeRadius i sign),
            (radius i sign x : E) = a i sign ↔ (x : P2) = signedTubeCorner i sign) ∧
          J.space = ((M reg).barycentricDualBlock s).space ∧
          Disjoint J.space (M fr).space ∧ J.space ∩ (M arc).space = {m} ∧
          (∀ v ∈ s, J.space ⊆ ((K.barycentricDualBlock {v}).link v).space) ∧
          (∀ i sign, a i sign ≠ m) ∧
          (∀ eps delta : Bool,
            let U := rad 0 delta ∪ rad 1 eps
            let O := Q eps delta ∩ q
            IsFinitePLBallPair P2 (Q eps delta) (O ∪ U) ∧
            IsFinitePLBallPair ℝ U {a 0 delta, a 1 eps} ∧
            IsFinitePLBallPair ℝ O {a 0 delta, a 1 eps} ∧
            U ∩ O = {a 0 delta, a 1 eps} ∧
            Q eps delta ∩ (M (sheet 0)).space = rad 0 delta ∧
            Q eps delta ∩ (M (sheet 1)).space = rad 1 eps ∧
            rad 0 delta ∩ rad 1 eps = {m}) ∧
          ∀ v : (M arc).vertices, (v : E) ∈ s → ∃ eta : Fin 2 → Bool,
            (∀ i : Fin 2,
              if eta i then
                B v (g (a i.rev false)) i.castSucc < 0 ∧
                  0 < B v (g (a i.rev true)) i.castSucc
              else
                0 < B v (g (a i.rev false)) i.castSucc ∧
                  B v (g (a i.rev true)) i.castSucc < 0) ∧
            ∀ (i : Fin 2) (sign : Bool) z, z ∈ J.space →
              ((if sign then 0 ≤ B p (g z) i.castSucc else B p (g z) i.castSucc ≤ 0) ↔
                if (if eta i then sign else !sign) then 0 ≤ B v (g z) i.castSucc
                  else B v (g z) i.castSucc ≤ 0) := by
  classical
  let J := K.barycentricDualBlock s
  let m := s.centroid ℝ id
  let q := (J.link m).space
  let I := fun i : Fin 2 => ((M (sheet i)).barycentricDualBlock s).space
  obtain ⟨p, T, hQ⟩ := exists_original_signed_tube_joint_quarters
    hAC hAR hAF S K F hF H hH g hg hgPL M hMK hfull reg fr arc sheet
      hreg hfr harc hsheet B hB s hs hcard
  let a : Fin 2 → Bool → E := fun i sign => (T i sign).centroid ℝ id
  let rad : Fin 2 → Bool → Set E := fun i sign => segment ℝ m (a i sign)
  let lam : Fin 2 → E → ℝ := fun i z => B p (g z) i.castSucc
  let side : Bool → ℝ → Prop := fun sign x => if sign then 0 ≤ x else x ≤ 0
  let Q : Bool → Bool → Set E := fun eps delta =>
    {z | z ∈ J.space ∧ side eps (lam 0 z) ∧ side delta (lam 1 z)}
  rcases hQ with ⟨hps, hpR, hJ, hJR, hJreg, hmiss, hJarc, hlinks,
    hcrossI, hI, hQuarter, hInter, hcover, hchange⟩
  have hInter' (eps delta : Bool) :
      Q eps delta ∩ Q eps (!delta) = rad 1 eps ∧
      Q eps delta ∩ Q (!eps) delta = rad 0 delta ∧
      Q eps delta ∩ Q (!eps) (!delta) = {m} := hInter eps delta
  have hIrad (i : Fin 2) : I i = rad i false ∪ rad i true := (hI i).2.2.1
  have hANe (i : Fin 2) (sign : Bool) : a i sign ≠ m := by
    obtain ⟨_, _, _, ha, _⟩ := (hI i).2.2.2.2 sign
    exact ha
  have hRadBall (i : Fin 2) (sign : Bool) :
      IsFinitePLBallPair ℝ (rad i sign) {m, a i sign} := by
    obtain ⟨_, _, _, _, hr, _⟩ := (hI i).2.2.2.2 sign
    exact hr
  choose er her herCenter herEnd using fun (i : Fin 2) (sign : Bool) =>
    (signedTube_radius_ball i sign).exists_marked_interval_homeomorph
      (hRadBall i sign) (signedTube_corner_ne_center i sign).symm (hANe i sign).symm
  have hExtensions (eps delta : Bool) :=
    signedTube_quarter_extension m a Q q eps delta
      (hQuarter eps delta).1 (hQuarter eps delta).2.2.1
      (hQuarter eps delta).2.2.2.1 (hQuarter eps delta).2.2.2.2.2.2
      er her herCenter herEnd
  choose f hf hkeep0 hkeep1 using hExtensions
  have hSrc0 (eps delta : Bool) : signedTubeRadius 0 delta ⊆ signedTubeQuarter eps delta :=
    fun _ hx => (signedTube_quarter_ball eps delta).1 (Or.inr (Or.inl hx))
  have hSrc1 (eps delta : Bool) : signedTubeRadius 1 eps ⊆ signedTubeQuarter eps delta :=
    fun _ hx => (signedTube_quarter_ball eps delta).1 (Or.inr (Or.inr hx))
  have hTgt0 (eps delta : Bool) : rad 0 delta ⊆ Q eps delta :=
    fun _ hx => (hQuarter eps delta).1.1 (Or.inr (Or.inl hx))
  have hTgt1 (eps delta : Bool) : rad 1 eps ⊆ Q eps delta :=
    fun _ hx => (hQuarter eps delta).1.1 (Or.inr (Or.inr hx))
  have hRad0 (eps delta : Bool) (x : signedTubeQuarter eps delta) :
      (x : P2) ∈ signedTubeRadius 0 delta ↔ (f eps delta x : E) ∈ rad 0 delta :=
    (f eps delta).mem_subset_iff_of_extension (er 0 delta)
      (hSrc0 eps delta) (hTgt0 eps delta)
      (fun z => Subtype.ext (hkeep0 eps delta z)) x
  have hRad1 (eps delta : Bool) (x : signedTubeQuarter eps delta) :
      (x : P2) ∈ signedTubeRadius 1 eps ↔ (f eps delta x : E) ∈ rad 1 eps :=
    (f eps delta).mem_subset_iff_of_extension (er 1 eps)
      (hSrc1 eps delta) (hTgt1 eps delta)
      (fun z => Subtype.ext (hkeep1 eps delta z)) x
  have hZero (eps delta : Bool) : (0, 0) ∈ signedTubeQuarter eps delta :=
    hSrc0 eps delta (left_mem_segment ℝ _ _)
  have hCenter (eps delta : Bool) :
      (f eps delta ⟨(0, 0), hZero eps delta⟩ : E) = m :=
    (hkeep0 eps delta ⟨(0, 0), left_mem_segment ℝ _ _⟩).trans
      ((herCenter 0 delta ⟨(0, 0), left_mem_segment ℝ _ _⟩).mpr rfl)
  have hCenterIff (eps delta : Bool) (x : signedTubeQuarter eps delta) :
      (x : P2) = (0, 0) ↔ (f eps delta x : E) = m := by
    constructor
    · intro hx
      exact (congrArg (fun z : signedTubeQuarter eps delta => (f eps delta z : E))
        (show x = ⟨(0, 0), hZero eps delta⟩ from Subtype.ext hx)).trans (hCenter eps delta)
    · intro hx
      exact congrArg Subtype.val ((f eps delta).injective
        (Subtype.ext (hx.trans (hCenter eps delta).symm)))
  have hoverlap (u v : Bool × Bool) (x : signedTubeQuarter u.1 u.2) :
      (x : P2) ∈ signedTubeQuarter v.1 v.2 ↔ (f u.1 u.2 x : E) ∈ Q v.1 v.2 := by
    rcases u with ⟨eps, delta⟩
    rcases v with ⟨eps', delta'⟩
    dsimp only at x ⊢
    by_cases heps : eps = eps'
    · subst eps'
      by_cases hdelta : delta = delta'
      · subst delta'
        exact iff_of_true x.property (f eps delta x).property
      · have hn : delta' = !delta := Bool.eq_not_of_ne (Ne.symm hdelta)
        subst delta'
        have hs : (x : P2) ∈ signedTubeQuarter eps (!delta) ↔
            (x : P2) ∈ signedTubeRadius 1 eps := by
          rw [← signedTube_quarter_inter_delta eps delta]
          simp only [mem_inter_iff, x.property, true_and]
        have ht : (f eps delta x : E) ∈ Q eps (!delta) ↔
            (f eps delta x : E) ∈ rad 1 eps := by
          rw [← (hInter' eps delta).1]
          simp only [mem_inter_iff, (f eps delta x).property, true_and]
        exact hs.trans ((hRad1 eps delta x).trans ht.symm)
    · have hn : eps' = !eps := Bool.eq_not_of_ne (Ne.symm heps)
      subst eps'
      by_cases hdelta : delta = delta'
      · subst delta'
        have hs : (x : P2) ∈ signedTubeQuarter (!eps) delta ↔
            (x : P2) ∈ signedTubeRadius 0 delta := by
          rw [← signedTube_quarter_inter_eps eps delta]
          simp only [mem_inter_iff, x.property, true_and]
        have ht : (f eps delta x : E) ∈ Q (!eps) delta ↔
            (f eps delta x : E) ∈ rad 0 delta := by
          rw [← (hInter' eps delta).2.1]
          simp only [mem_inter_iff, (f eps delta x).property, true_and]
        exact hs.trans ((hRad0 eps delta x).trans ht.symm)
      · have hn : delta' = !delta := Bool.eq_not_of_ne (Ne.symm hdelta)
        subst delta'
        have hs : (x : P2) ∈ signedTubeQuarter (!eps) (!delta) ↔
            (x : P2) = (0, 0) := by
          rw [← mem_singleton_iff, ← signedTube_quarter_inter_opposite eps delta]
          simp only [mem_inter_iff, x.property, true_and]
        have ht : (f eps delta x : E) ∈ Q (!eps) (!delta) ↔
            (f eps delta x : E) = m := by
          rw [← mem_singleton_iff, ← (hInter' eps delta).2.2]
          simp only [mem_inter_iff, (f eps delta x).property, true_and]
        exact hs.trans ((hCenterIff eps delta x).trans ht.symm)
  have hagree (u v : Bool × Bool) (x : P2)
      (hx : x ∈ signedTubeQuarter u.1 u.2) (hy : x ∈ signedTubeQuarter v.1 v.2) :
      (f u.1 u.2 ⟨x, hx⟩ : E) = f v.1 v.2 ⟨x, hy⟩ := by
    rcases u with ⟨eps, delta⟩
    rcases v with ⟨eps', delta'⟩
    dsimp only at hx hy ⊢
    by_cases heps : eps = eps'
    · subst eps'
      by_cases hdelta : delta = delta'
      · subst delta'
        rfl
      · have hn : delta' = !delta := Bool.eq_not_of_ne (Ne.symm hdelta)
        subst delta'
        have hr : x ∈ signedTubeRadius 1 eps :=
          (signedTube_quarter_inter_delta eps delta).subset ⟨hx, hy⟩
        exact (hkeep1 eps delta ⟨x, hr⟩).trans (hkeep1 eps (!delta) ⟨x, hr⟩).symm
    · have hn : eps' = !eps := Bool.eq_not_of_ne (Ne.symm heps)
      subst eps'
      by_cases hdelta : delta = delta'
      · subst delta'
        have hr : x ∈ signedTubeRadius 0 delta :=
          (signedTube_quarter_inter_eps eps delta).subset ⟨hx, hy⟩
        exact (hkeep0 eps delta ⟨x, hr⟩).trans (hkeep0 (!eps) delta ⟨x, hr⟩).symm
      · have hn : delta' = !delta := Bool.eq_not_of_ne (Ne.symm hdelta)
        subst delta'
        have hz : x = (0, 0) :=
          (signedTube_quarter_inter_opposite eps delta).subset ⟨hx, hy⟩
        exact ((hCenterIff eps delta ⟨x, hx⟩).mp hz).trans
          ((hCenterIff (!eps) (!delta) ⟨x, hy⟩).mp hz).symm
  obtain ⟨G, hG, hGkeep⟩ := Homeomorph.exists_iUnion_finitePL
    (fun u : Bool × Bool => signedTubeQuarter u.1 u.2)
    (fun u : Bool × Bool => Q u.1 u.2)
    (fun u => f u.1 u.2) (fun u => hf u.1 u.2) hoverlap hagree
  have hSource : (⋃ u : Bool × Bool, signedTubeQuarter u.1 u.2) = signedTubeDiamond := by
    ext x
    simp only [signedTubeDiamond, mem_iUnion, Prod.exists]
  have hTarget : (⋃ u : Bool × Bool, Q u.1 u.2) = J.space := by
    calc
      (⋃ u : Bool × Bool, Q u.1 u.2) = ⋃ eps, ⋃ delta, Q eps delta := by
        ext x
        simp only [mem_iUnion, Prod.exists]
      _ = J.space := hcover
  let G' : signedTubeDiamond ≃ₜ J.space :=
    (Homeomorph.setCongr hSource.symm).trans (G.trans (Homeomorph.setCongr hTarget))
  have hG' : G'.IsFinitePL := hG.setCongr hSource hTarget
  have hKeep (eps delta : Bool) (x : signedTubeQuarter eps delta) :
      (G' ⟨x, mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, x.property⟩⟩⟩ : E) =
        f eps delta x := hGkeep (eps, delta) x
  have hGlobalSrc0 (sign : Bool) : signedTubeRadius 0 sign ⊆ signedTubeDiamond :=
    fun x hx => mem_iUnion.mpr ⟨false, mem_iUnion.mpr ⟨sign, hSrc0 false sign hx⟩⟩
  have hGlobalSrc1 (sign : Bool) : signedTubeRadius 1 sign ⊆ signedTubeDiamond :=
    fun x hx => mem_iUnion.mpr ⟨sign, mem_iUnion.mpr ⟨false, hSrc1 sign false hx⟩⟩
  have hGlobalTgt0 (sign : Bool) : rad 0 sign ⊆ J.space :=
    fun _ hx => (hTgt0 false sign hx).1
  have hGlobalTgt1 (sign : Bool) : rad 1 sign ⊆ J.space :=
    fun _ hx => (hTgt1 sign false hx).1
  have hGlobalRad0 (sign : Bool) (x : signedTubeDiamond) :
      (x : P2) ∈ signedTubeRadius 0 sign ↔ (G' x : E) ∈ rad 0 sign :=
    G'.mem_subset_iff_of_extension (er 0 sign) (hGlobalSrc0 sign) (hGlobalTgt0 sign)
      (fun z => Subtype.ext ((hKeep false sign ⟨z, hSrc0 false sign z.property⟩).trans
        (hkeep0 false sign z))) x
  have hGlobalRad1 (sign : Bool) (x : signedTubeDiamond) :
      (x : P2) ∈ signedTubeRadius 1 sign ↔ (G' x : E) ∈ rad 1 sign :=
    G'.mem_subset_iff_of_extension (er 1 sign) (hGlobalSrc1 sign) (hGlobalTgt1 sign)
      (fun z => Subtype.ext ((hKeep sign false ⟨z, hSrc1 sign false z.property⟩).trans
        (hkeep1 sign false z))) x
  refine ⟨p, T, G', hG', ?_, ?_, ?_, ?_, ?_, ?_, hps,
    f, er, hf, her, hKeep, ?_, herCenter, herEnd,
    hJreg, hmiss, hJarc, hlinks, hANe, hQuarter, hchange⟩
  · intro eps delta x
    rw [hKeep]
    exact (f eps delta x).property
  · intro eps delta x
    exact iff_of_true x.property (by rw [hKeep]; exact (f eps delta x).property)
  · intro i x
    fin_cases i
    · change (x : P2) ∈ signedTubeRadius 0 false ∪ signedTubeRadius 0 true ↔ (G' x : E) ∈ I 0
      rw [hIrad]
      exact or_congr (hGlobalRad0 false x) (hGlobalRad0 true x)
    · change (x : P2) ∈ signedTubeRadius 1 false ∪ signedTubeRadius 1 true ↔ (G' x : E) ∈ I 1
      rw [hIrad]
      exact or_congr (hGlobalRad1 false x) (hGlobalRad1 true x)
  · exact (hKeep false false ⟨(0, 0), signedTube_center_mem⟩).trans (hCenter false false)
  · intro eps delta
    exact (hQuarter eps delta).2.2.2.2.1
  · intro eps delta
    exact (hQuarter eps delta).2.2.2.2.2.1

  · intro i sign x
    fin_cases i
    · exact (hKeep false sign ⟨x, hSrc0 false sign x.property⟩).trans (hkeep0 false sign x)
    · exact (hKeep sign false ⟨x, hSrc1 sign false x.property⟩).trans (hkeep1 sign false x)

open Classical in





theorem exists_original_signed_tube_joint_maps
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R C A : Set X}
    (hAC : A ⊆ interior C) (hAR : A ⊆ R) (hAF : (A ∩ frontier R).Finite)
    (S : Fin 2 → Set X) (K : SimplicialComplex ℝ E) [Fintype K.faces]
    (F : X → E) (hF : Continuous F) (H : C ≃ₜ K.space)
    (hH : ∀ x : C, (H x : E) = F x) (g : E → C)
    (hg : ∀ z : K.space, (g z : X) = (H.symm z : X))
    (hgPL : PolyhedralPLInCharts e (fun z => (g z : X)) K.space)
    (M : κ → SimplicialComplex ℝ E) [∀ i, Fintype (M i).faces]
    (hMK : ∀ i, M i ≤ K)
    (hfull : ∀ i t, t ∈ K.faces → (∀ v ∈ t, v ∈ (M i).vertices) → t ∈ (M i).faces)
    (reg fr arc : κ) (sheet : Fin 2 → κ)
    (hreg : ∀ z ∈ K.space, z ∈ (M reg).space ↔ (g z : X) ∈ R)
    (hfr : ∀ z ∈ K.space, z ∈ (M fr).space ↔ (g z : X) ∈ frontier R)
    (harc : ∀ z ∈ K.space, z ∈ (M arc).space ↔ (g z : X) ∈ A)
    (hsheet : ∀ i z, z ∈ K.space →
      (z ∈ (M (sheet i)).space ↔ (g z : X) ∈ S i))
    (B : (M arc).vertices → OpenPartialHomeomorph X V3)
    (hB : ∀ p : (M arc).vertices,
      MapsTo (fun z => (g z : X)) (K.closedStar p).space (B p).source ∧
      (K.closedStar p).AffineOnFaces (fun z => B p (g z)) ∧
      (∀ y ∈ (B p).source, y ∈ A ↔ y ∈ R ∧ B p y 0 = 0 ∧ B p y 1 = 0) ∧
      ∀ i y, y ∈ (B p).source →
        (y ∈ S i ↔ y ∈ R ∧ B p y i.castSucc = 0))
    (s : Finset E) (hs : s ∈ (M arc).faces) (hcard : s.card = 2) :
    let J := K.barycentricDualBlock s
    let m := s.centroid ℝ id
    let q := (J.link m).space
    let I := fun i : Fin 2 => ((M (sheet i)).barycentricDualBlock s).space
    ∃ (p : (M arc).vertices) (T : Fin 2 → Bool → Finset E),
      let a := fun i sign => (T i sign).centroid ℝ id
      let rad := fun i sign => segment ℝ m (a i sign)
      let Q := fun eps delta : Bool => {z | z ∈ J.space ∧
        (if eps then 0 ≤ B p (g z) 0 else B p (g z) 0 ≤ 0) ∧
        if delta then 0 ≤ B p (g z) 1 else B p (g z) 1 ≤ 0}
      ∃ (H : signedTubeDiamond ≃ₜ J.space), H.IsFinitePL ∧
        (∀ eps delta (x : signedTubeQuarter eps delta),
          (H ⟨x, by exact mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, x.property⟩⟩⟩ : E) ∈
            Q eps delta) ∧
        (∀ eps delta (x : signedTubeQuarter eps delta),
          (x : P2) ∈ signedTubeQuarter eps delta ↔
            (H ⟨x, by exact mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, x.property⟩⟩⟩ : E) ∈
              Q eps delta) ∧
        (∀ (i : Fin 2) (x : signedTubeDiamond),
          (x : P2) ∈ signedTubeSheet i ↔
            (H x : E) ∈ I i) ∧
        (H ⟨(0, 0), by
          exact mem_iUnion.mpr ⟨false, mem_iUnion.mpr ⟨false,
            signedTube_center_mem⟩⟩⟩ : E) = m ∧
        (∀ eps delta, Q eps delta ∩ (M (sheet 0)).space =
          rad 0 delta) ∧
        (∀ eps delta, Q eps delta ∩ (M (sheet 1)).space =
          rad 1 eps) := by
  obtain ⟨p, T, G, hG, hquarter, hquarterOn, hsheet, hcenter, hrad0, hrad1, _⟩ :=
    exists_original_signed_tube_joint_boundary_maps
      hAC hAR hAF S K F hF H hH g hg hgPL M hMK hfull reg fr arc sheet
      hreg hfr harc hsheet B hB s hs hcard
  exact ⟨p, T, G, hG, hquarter, hquarterOn, hsheet, hcenter, hrad0, hrad1⟩

end PoincareConjecture.M76.Dehn
