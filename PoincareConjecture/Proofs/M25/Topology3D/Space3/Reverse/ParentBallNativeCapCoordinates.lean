import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReferenceModel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.NorthSphereChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import Mathlib.Topology.MetricSpace.Thickening










set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D


noncomputable def referenceCapSphereChart
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1) :
    OpenPartialHomeomorph E2 UnitTwoSphere where
  toFun := fun X => northSpherePoint ((referenceCapScale a)⁻¹ • X)
  invFun := fun q => referenceCapScale a • northSphereCoordinate q
  source := univ
  target := northSphereDomain
  map_source' X _ := northSpherePoint_mem_domain _
  map_target' _ _ := mem_univ _
  left_inv' X _ := by
    rw [northSphereCoordinate_point, smul_smul,
      mul_inv_cancel₀ (referenceCapScale_pos a ha).ne', one_smul]
  right_inv' q hq := by
    rw [smul_smul, inv_mul_cancel₀ (referenceCapScale_pos a ha).ne', one_smul]
    exact northSpherePoint_coordinate hq
  open_source := isOpen_univ
  open_target := northSphereDomain_isOpen
  continuousOn_toFun :=
    (northSpherePoint_contMDiff.comp
      (contDiff_const_smul (referenceCapScale a)⁻¹).contMDiff).continuous.continuousOn
  continuousOn_invFun :=
    (continuousOn_const (c := referenceCapScale a)).smul
      northSphereCoordinate_contMDiffOn.continuousOn


theorem referenceCapSphereChart_spec
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1) :
    let P := referenceCapSphereChart a ha
    P.source = univ ∧ P.target = northSphereDomain ∧
    (∀ X : E2, (P X : E3) = referenceCapPoint a X) ∧
    (∀ q : UnitTwoSphere,
      P.symm q = referenceCapScale a • northSphereCoordinate q) ∧
    ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ P P.source ∧
    ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ P.symm P.target ∧
    P '' closedBall (0 : E2) 1 =
      {q : UnitTwoSphere | a ≤ (heightCoordinates (q : E3)).2} := by
  let P := referenceCapSphereChart a ha
  have hpoint (X : E2) : (P X : E3) = referenceCapPoint a X := by
    let c := referenceCapScale a
    have hc : 0 < c := referenceCapScale_pos a ha
    have hd : c ^ 2 + ‖X‖ ^ 2 ≠ 0 :=
      ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg ‖X‖))
    have hn : ‖c⁻¹ • X‖ ^ 2 = ‖X‖ ^ 2 / c ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
      ring
    change northSphereVector (c⁻¹ • X) = referenceCapPoint a X
    apply heightCoordinates.injective
    rw [northSphereVector, referenceCapPoint, heightCoordinates.apply_symm_apply,
      heightCoordinates.apply_symm_apply]
    change ((2 / (1 + ‖c⁻¹ • X‖ ^ 2)) • (c⁻¹ • X),
      (1 - ‖c⁻¹ • X‖ ^ 2) / (1 + ‖c⁻¹ • X‖ ^ 2)) =
        ((2 * c / (c ^ 2 + ‖X‖ ^ 2)) • X,
          (c ^ 2 - ‖X‖ ^ 2) / (c ^ 2 + ‖X‖ ^ 2))
    rw [hn, smul_smul]
    apply Prod.ext
    · congr 1
      field_simp [hc.ne', hd]
    · field_simp [hc.ne', hd]
  have hsmooth : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ P P.source :=
    (northSpherePoint_contMDiff.comp
      (contDiff_const_smul (referenceCapScale a)⁻¹).contMDiff).contMDiffOn
  have hinverse : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ P.symm P.target :=
    (contMDiffOn_const : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun _ : UnitTwoSphere => referenceCapScale a) northSphereDomain).smul
        northSphereCoordinate_contMDiffOn
  refine ⟨rfl, rfl, hpoint, fun _ => rfl, hsmooth, hinverse, ?_⟩
  ext q
  constructor
  · rintro ⟨X, hX, rfl⟩
    change a ≤ (heightCoordinates (P X : E3)).2
    rw [hpoint X]
    exact (referenceCapPoint_cap_iff a ha X).mpr (mem_closedBall_zero_iff.mp hX)
  · intro hq
    have himage : (q : E3) ∈ referenceCapPoint a '' closedBall (0 : E2) 1 := by
      rw [referenceCapPoint_image_closedBall a ha]
      exact ⟨norm_eq_of_mem_sphere q, hq⟩
    obtain ⟨X, hX, heq⟩ := himage
    exact ⟨X, hX, Subtype.ext ((hpoint X).trans heq)⟩


noncomputable def nativeCapSourceChart
    (ψ : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (tag : SurgeryCapTag ψ u)
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (g : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞) :
    OpenPartialHomeomorph E2 UnitTwoSphere :=
  ((referenceCapSphereChart a ha).trans
    g.symm.toHomeomorph.toOpenPartialHomeomorph).trans tag.sourceChart.symm


theorem nativeCapSourceChart_spec
    (ψ : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (tag : SurgeryCapTag ψ u) (A : BallNeighborhoodChart E3 E3)
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (g : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)
    (hg : ∀ q : UnitTwoSphere, A.chart (g q : E3) = ψ (q, 0))
    (hnormalized : A.chart ''
      {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2} = tag.cap) :
    let P := referenceCapSphereChart a ha
    let Q := nativeCapSourceChart ψ u tag a ha g
    Q.source = {X : E2 | g.symm (P X) ∈ tag.sourceChart.target} ∧
    Q.target = {q : UnitTwoSphere | q ∈ tag.sourceChart.source ∧
      g (tag.sourceChart q) ∈ northSphereDomain} ∧
    (∀ X : E2, Q X = tag.sourceChart.symm (g.symm (P X))) ∧
    (∀ q : UnitTwoSphere, Q.symm q =
      referenceCapScale a • northSphereCoordinate (g (tag.sourceChart q))) ∧
    ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ Q Q.source ∧
    ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ Q.symm Q.target ∧
    closedBall (0 : E2) 1 ⊆ Q.source ∧
    Q '' closedBall (0 : E2) 1 =
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
    ∃ R : ℝ, 1 < R ∧ closedBall (0 : E2) R ⊆ Q.source ∧
      (∀ X : E2, ‖X‖ ≤ R →
        (heightCoordinates (Q X : E3)).2 < tag.overlapWidth) ∧
      ∀ X : E2, ‖X‖ ≤ R →
        tag.profile.capMap tag.tube tag.cutHeight tag.sign tag.removal
          tag.scale (Q X) = A.chart (referenceCapPoint a X) := by
  let P := referenceCapSphereChart a ha
  let J := P.trans g.symm.toHomeomorph.toOpenPartialHomeomorph
  let Q := nativeCapSourceChart ψ u tag a ha g
  obtain ⟨hPs, hPt, hP, hPi, hPsm, hPism, hPcap⟩ := referenceCapSphereChart_spec a ha
  have hQs : Q.source = {X : E2 | g.symm (P X) ∈ tag.sourceChart.target} := by
    ext X
    change ((X ∈ P.source ∧ P X ∈ (univ : Set UnitTwoSphere)) ∧
      g.symm (P X) ∈ tag.sourceChart.target) ↔ _
    rw [hPs]
    simp only [mem_univ, true_and, mem_ofPred_eq]
  have hQt : Q.target = {q : UnitTwoSphere | q ∈ tag.sourceChart.source ∧
      g (tag.sourceChart q) ∈ northSphereDomain} := by
    ext q
    change (q ∈ tag.sourceChart.source ∧
      (tag.sourceChart q ∈ (univ : Set UnitTwoSphere) ∧
        g (tag.sourceChart q) ∈ P.target)) ↔ _
    rw [hPt]
    simp only [mem_univ, true_and, mem_ofPred_eq]
  have hJ : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ J J.source :=
    g.symm.contMDiff.comp_contMDiffOn (hPsm.mono inter_subset_left)
  have hJi : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ J.symm J.target :=
    hPism.comp g.contMDiff.contMDiffOn (fun _ hx => hx.2)
  have hQ : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ Q Q.source :=
    tag.source_inverse.comp (hJ.mono inter_subset_left) (fun _ hx => hx.2)
  have hQi : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ Q.symm Q.target :=
    hJi.comp (tag.source_smooth.mono inter_subset_left) (fun _ hx => hx.2)
  have hmatch (X : E2) (q : UnitTwoSphere)
      (hq : (heightCoordinates (q : E3)).2 ≤ 0)
      (heq : A.chart (P X : E3) = ψ (tag.sourceChart q, 0)) :
      X ∈ Q.source ∧ Q X = q := by
    have hEq : P X = g (tag.sourceChart q) := by
      apply Subtype.ext
      exact A.chart.injOn
        (A.closedBall_subset_source (sphere_subset_closedBall (P X).2))
        (A.closedBall_subset_source (sphere_subset_closedBall (g (tag.sourceChart q)).2))
        (heq.trans (hg _).symm)
    have hpull : g.symm (P X) = tag.sourceChart q := by
      rw [hEq, g.symm_apply_apply]
    have hqsource := tag.south_mem_source q hq
    constructor
    · rw [hQs]
      change g.symm (P X) ∈ tag.sourceChart.target
      rw [hpull]
      exact tag.sourceChart.map_source hqsource
    · change tag.sourceChart.symm (g.symm (P X)) = q
      rw [hpull]
      exact tag.sourceChart.left_inv hqsource
  have hforward (X : E2) (hX : X ∈ closedBall (0 : E2) 1) :
      X ∈ Q.source ∧ (heightCoordinates (Q X : E3)).2 ≤ 0 := by
    have hPX : a ≤ (heightCoordinates (P X : E3)).2 := by
      have hh : P X ∈ P '' closedBall (0 : E2) 1 := mem_image_of_mem P hX
      rwa [hPcap] at hh
    have hcap : A.chart (P X : E3) ∈ tag.cap := by
      rw [← hnormalized]
      exact ⟨(P X : E3), ⟨norm_eq_of_mem_sphere (P X), hPX⟩, rfl⟩
    change A.chart (P X : E3) ∈
      (fun q : UnitTwoSphere => ψ (q, 0)) ''
        (tag.sourceChart '' {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}) at hcap
    obtain ⟨_, ⟨q, hq, rfl⟩, heq⟩ := hcap
    obtain ⟨hsource, hQq⟩ := hmatch X q hq heq.symm
    exact ⟨hsource, hQq.symm ▸ hq⟩
  have hclosed : closedBall (0 : E2) 1 ⊆ Q.source := fun X hX => (hforward X hX).1
  have himage : Q '' closedBall (0 : E2) 1 =
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} := by
    ext q
    constructor
    · rintro ⟨X, hX, rfl⟩
      exact (hforward X hX).2
    · intro hq
      have hcap : ψ (tag.sourceChart q, 0) ∈ tag.cap :=
        ⟨tag.sourceChart q, ⟨q, hq, rfl⟩, rfl⟩
      rw [← hnormalized] at hcap
      obtain ⟨y, hy, heq⟩ := hcap
      have hyimage : y ∈ referenceCapPoint a '' closedBall (0 : E2) 1 := by
        rwa [referenceCapPoint_image_closedBall a ha]
      obtain ⟨X, hX, hxy⟩ := hyimage
      have hPX : A.chart (P X : E3) = ψ (tag.sourceChart q, 0) := by
        rw [hP X, hxy]
        exact heq
      exact ⟨X, hX, (hmatch X q hq hPX).2⟩
  let V : Set UnitTwoSphere := {q | (heightCoordinates (q : E3)).2 < tag.overlapWidth}
  let U : Set E2 := Q.source ∩ Q ⁻¹' V
  have hV : IsOpen V := isOpen_lt
    ((heightCoordinates.continuous.comp continuous_subtype_val).snd) continuous_const
  have hU : IsOpen U := Q.isOpen_inter_preimage hV
  have hKU : closedBall (0 : E2) 1 ⊆ U := by
    intro X hX
    exact ⟨hclosed hX, lt_of_le_of_lt (hforward X hX).2 tag.overlap_pos⟩
  obtain ⟨d, hd, hsub⟩ := (isCompact_closedBall (0 : E2) 1).exists_thickening_subset_open hU hKU
  rw [thickening_closedBall hd zero_le_one] at hsub
  let R : ℝ := 1 + d / 2
  have hR : 1 < R := by dsimp only [R]; linarith
  have hRU : closedBall (0 : E2) R ⊆ U := by
    intro X hX
    apply hsub
    apply mem_ball_zero_iff.mpr
    have hh := mem_closedBall_zero_iff.mp hX
    dsimp only [R] at hh
    linarith
  refine ⟨hQs, hQt, fun _ => rfl, ?_, hQ, hQi, hclosed, himage,
    R, hR, fun X hX => (hRU hX).1, ?_, ?_⟩
  · intro q
    exact hPi (g (tag.sourceChart q))
  · intro X hX
    exact (hRU (mem_closedBall_zero_iff.mpr hX)).2
  · intro X hX
    have hXu := hRU (mem_closedBall_zero_iff.mpr hX)
    have hXt : g.symm (P X) ∈ tag.sourceChart.target := by
      have hs := hXu.1
      rwa [hQs] at hs
    have hinv : tag.sourceChart (Q X) = g.symm (P X) := tag.sourceChart.right_inv hXt
    rw [← tag.central_eq (Q X) hXu.2, hinv, ← hg (g.symm (P X)),
      g.apply_symm_apply, hP X]

end PoincareConjecture.M25.Topology3D
