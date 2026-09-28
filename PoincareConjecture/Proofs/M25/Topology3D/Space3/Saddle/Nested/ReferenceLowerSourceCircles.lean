import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceHighRegularity
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedReferenceFillings
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedReferenceCollar
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularHorizontalTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceCirclePullback

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace Topology Matrix

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

theorem exists_reference_lower_source_circles
    (ws wm d a : ℝ)
    (hwslo : (1 : ℝ) / 2 < ws) (hwshi : ws < 3 / 4)
    (hwsroot : (2 - 1 / ws) * Real.sqrt (1 - ws ^ 2) = 1 / 32)
    (hwmlo : 0 < wm) (hwmhi : wm < 1 / 2)
    (hwmroot : (2 - 1 / wm) * Real.sqrt (1 - wm ^ 2) = -(1 / 32))
    (ha : (17 : ℝ) / 16 ≤ a) :
    let U : E2 → ℝ := fun x =>
      ‖x‖ ^ 2 + Real.sqrt (1 - ‖x‖ ^ 2) + x 0 / 32
    let k : ℝ := U !₂[-Real.sqrt (1 - ws ^ 2), 0]
    a < k →
    let j : UnitTwoSphere → E3 := fun q => nestedReferenceDiffeomorph d (q : E3)
    let H : UnitTwoSphere → ℝ := fun q => (heightCoordinates (j q)).2
    let m : ℝ := ((17 / 16 + d) + (a + d)) / 2
    ∃ (B0 : Fin 2 → BallNeighborhoodChart E2 E2)
      (T : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
      (eta : ℝ) (q : Fin 2 → UnitCircle → UnitTwoSphere),
      let C : Fin 2 → ℝ → UnitCircle → E2 := fun i z theta =>
        T z ((B0 i).chart (theta : E2))
      let B : ℝ → Fin 2 → BallNeighborhoodChart E2 E2 := fun z i =>
        (B0 i).mapDiffeomorph (T z)
      (∀ i : Fin 2, (B0 i).chart.source = univ ∧ (B0 i).chart.target = univ) ∧
      (B0 0).closedRegion ⊆ (B0 1).inside ∧
      {x : E2 | heightCoordinates.symm (x, 17 / 16 + d) ∈
        (nestedReferenceBallChart d).closedRegion} =
          (B0 1).closedRegion \ (B0 0).inside ∧
      {x : E2 | heightCoordinates.symm (x, 17 / 16 + d) ∈
        (nestedReferenceBallChart d).inside} =
          (B0 1).inside \ (B0 0).closedRegion ∧
      (∀ p : UnitTwoSphere, H p ∈ Icc (17 / 16 + d) (a + d) →
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) H p ≠ 0) ∧
      0 < eta ∧ Icc (17 / 16 + d) (a + d) ⊆ Ioo (m - eta) (m + eta) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E2 => T p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E2 => (T p.1).symm p.2) ∧
      (∀ x : E2, T (17 / 16 + d) x = x) ∧
      (∀ i : Fin 2,
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
          (fun p : ℝ × UnitCircle => C i p.1 p.2) ∧
        ∀ z : ℝ, IsPlanarEmbedding (C i z) ∧ range (C i z) = (B z i).boundary) ∧
      (∀ z : ℝ, (B z 0).closedRegion ⊆ (B z 1).inside ∧
        Disjoint (B z 0).boundary (B z 1).boundary) ∧
      (∀ z ∈ Ioo (m - eta) (m + eta), ∀ x : E2,
        (heightCoordinates.symm (T z x, z) ∈ range j ↔
          heightCoordinates.symm (x, 17 / 16 + d) ∈ range j)) ∧
      (∀ z ∈ Ioo (m - eta) (m + eta),
        {x : E2 | heightCoordinates.symm (x, z) ∈ range j} =
          ⋃ i : Fin 2, (B z i).boundary) ∧
      (∀ i : Fin 2,
        ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Function.Injective (q i) ∧
        ∀ theta : UnitCircle,
          Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q i) theta)) ∧
      (∀ i l : Fin 2, i ≠ l → Disjoint (range (q i)) (range (q l))) ∧
      (⋃ i : Fin 2, range (q i)) = {p : UnitTwoSphere | H p = a + d} ∧
      ∀ (i : Fin 2) (theta : UnitCircle),
        j (q i theta) = heightCoordinates.symm (C i (a + d) theta, a + d) := by
  classical
  let U : E2 → ℝ := fun x =>
    ‖x‖ ^ 2 + Real.sqrt (1 - ‖x‖ ^ 2) + x 0 / 32
  let k : ℝ := U !₂[-Real.sqrt (1 - ws ^ 2), 0]
  change a < k → _
  intro hak
  let j : UnitTwoSphere → E3 := fun q => nestedReferenceDiffeomorph d (q : E3)
  let H : UnitTwoSphere → ℝ := fun q => (heightCoordinates (j q)).2
  let h0 : ℝ := 17 / 16 + d
  let b : ℝ := a + d
  let m : ℝ := (h0 + b) / 2
  obtain ⟨Bi, Bo, his, hit, hos, hot, _, _, _, _, hnested, hbase⟩ :=
    exists_nestedReference_lower_fillings
  obtain ⟨hclosed, hinside, hboundary, hbaseReg⟩ := hbase d
  let B0 : Fin 2 → BallNeighborhoodChart E2 E2 := ![Bi, Bo]
  have hB0 (i : Fin 2) :
      (B0 i).chart.source = univ ∧ (B0 i).chart.target = univ := by
    fin_cases i
    · exact ⟨his, hit⟩
    · exact ⟨hos, hot⟩
  have hnest0 : (B0 0).closedRegion ⊆ (B0 1).inside := hnested
  have hdis0 : Disjoint (B0 0).boundary (B0 1).boundary := by
    apply disjoint_left.mpr
    intro x hx hy
    exact disjoint_left.mp (B0 1).inside_disjoint_boundary
      (hnest0 (image_mono sphere_subset_closedBall hx)) hy
  obtain ⟨_, _, hkhi, hmulo, _, _, _, _, _, hnoncrit, _⟩ :=
    reference_high_sphere_regularity ws wm d hwslo hwshi hwsroot hwmlo hwmhi hwmroot
  have hreg (p : UnitTwoSphere) (hp : H p ∈ Icc h0 b) :
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) H p ≠ 0 := by
    by_cases heq : H p = h0
    · exact hbaseReg p heq
    · apply hnoncrit p
      · have hlt : h0 < H p := lt_of_le_of_ne hp.1 (Ne.symm heq)
        change 17 / 16 < H p - d
        dsimp only [h0] at hlt
        linarith only [hlt]
      · intro he
        change H p = k + d at he
        dsimp only [b] at hp
        linarith only [he, hp.2, hak]
      · intro he
        dsimp only [b] at hp
        change k < 5 / 4 at hkhi
        change H p = _ at he
        linarith only [he, hp.2, hak, hkhi, hmulo]
  let psi : UnitTwoSphere × ℝ → E3 := fun p =>
    nestedReferenceDiffeomorph d ((1 + p.2) • (p.1 : E3))
  have hpsi0 : (fun q : UnitTwoSphere => psi (q, 0)) = j := by
    funext q
    simp only [psi, j, add_zero, one_smul]
  obtain ⟨hpsi, hS, _, _⟩ := exists_nestedReference_collar d
  change IsCollarEmbedding psi at hpsi
  have hjS : range j = (nestedReferenceBallChart d).boundary := by
    simpa only [← hpsi0] using hS
  have hji : Injective j := (nestedReferenceDiffeomorph d).injective.comp Subtype.val_injective
  let u0 : UnitTwoSphere := ⟨EuclideanSpace.single (2 : Fin 3) 1, by simp⟩
  have hL : heightPlaneCoordinates u0 = heightCoordinates := by
    apply ContinuousLinearEquiv.ext
    funext y
    change heightCoordinates
      ((ℝ ∙ ((u0 : E3) - EuclideanSpace.single (2 : Fin 3) 1))ᗮ.reflection y) =
        heightCoordinates y
    rw [Submodule.reflection_mem_subspace_eq_self (by simp [u0])]
  have hheight : (fun p : UnitTwoSphere => ⟪(u0 : E3), psi (p, 0)⟫_ℝ) = H := by
    funext p
    rw [← heightPlaneCoordinates_snd u0, hL, congrFun hpsi0 p]
  have hab : h0 ≤ b := by
    change 17 / 16 + d ≤ a + d
    linarith only [ha]
  obtain ⟨eta, heta, hI, Phi, hPhi, hPhii, _, _, hPhiLevel⟩ :=
    exists_regular_collar_horizontal_transport psi hpsi u0 h0 b hab
      (by
        intro p hp
        have hp' : H p ∈ Icc h0 b := by
          rw [← congrFun hheight p]
          exact hp
        rw [hheight]
        exact hreg p hp')
  simp only [hL, hpsi0] at hPhiLevel
  let T : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
    fun z => (Phi h0).symm.trans (Phi z)
  let c0 : Fin 2 → UnitCircle → E2 := fun i theta => (B0 i).chart (theta : E2)
  let C : Fin 2 → ℝ → UnitCircle → E2 := fun i z theta => T z (c0 i theta)
  let B : ℝ → Fin 2 → BallNeighborhoodChart E2 E2 := fun z i =>
    (B0 i).mapDiffeomorph (T z)
  have hTs : ContDiff ℝ ∞ (fun p : ℝ × E2 => T p.1 p.2) :=
    hPhi.comp (contDiff_fst.prodMk ((Phi h0).symm.contDiff.comp contDiff_snd))
  have hTi : ContDiff ℝ ∞ (fun p : ℝ × E2 => (T p.1).symm p.2) :=
    (Phi h0).contDiff.comp hPhii
  have hT0 (x : E2) : T h0 x = x := (Phi h0).apply_symm_apply x
  let : Fact (Module.finrank ℝ E2 = 1 + 1) := ⟨by simp [E2]⟩
  have hc0 (i : Fin 2) : IsPlanarEmbedding (c0 i) := by
    have hcs : ContDiff ℝ ∞ (B0 i).chart :=
      contDiffOn_univ.mp (by simpa only [(hB0 i).1] using (B0 i).smooth)
    have hci : ContDiff ℝ ∞ (B0 i).chart.symm :=
      contDiffOn_univ.mp (by simpa only [(hB0 i).2] using (B0 i).smooth_symm)
    have hcm : (B0 i).chart.MDifferentiable 𝓘(ℝ, E2) 𝓘(ℝ, E2) :=
      ⟨hcs.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn,
        hci.contMDiff.mdifferentiable (by simp) |>.mdifferentiableOn⟩
    have hsource (theta : UnitCircle) : (theta : E2) ∈ (B0 i).chart.source :=
      (B0 i).closedBall_subset_source (sphere_subset_closedBall theta.property)
    refine ⟨hcs.contMDiff.comp contMDiff_coe_sphere, ?_, ?_⟩
    · intro theta xi heq
      exact Subtype.ext ((B0 i).chart.injOn (hsource theta) (hsource xi) heq)
    · intro theta
      change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2)
        ((B0 i).chart ∘ fun xi : UnitCircle => (xi : E2)) theta)
      rw [mfderiv_comp theta (hcs.contMDiff.mdifferentiable (by simp) _)
        ((contMDiff_coe_sphere (m := ∞)).mdifferentiable (by simp) theta)]
      apply (hcm.mfderiv_injective (hsource theta)).comp
      convert! injective_mvfderiv_subtypeVal_sphere theta
  have hc0range (i : Fin 2) : range (c0 i) = (B0 i).boundary := by
    ext x
    constructor
    · rintro ⟨theta, rfl⟩
      exact ⟨(theta : E2), theta.property, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨(⟨v, hv⟩ : UnitCircle), rfl⟩
  have hlevel0 : {x : E2 | heightCoordinates.symm (x, h0) ∈ range j} =
      ⋃ i : Fin 2, (B0 i).boundary := by
    rw [hjS]
    change {x : E2 | heightCoordinates.symm (x, 17 / 16 + d) ∈
      (nestedReferenceBallChart d).boundary} = _
    rw [hboundary]
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact mem_iUnion.mpr ⟨0, hx⟩
      · exact mem_iUnion.mpr ⟨1, hx⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
  have hmapEmbedding
      (G : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
      (v : UnitCircle → E2) (hv : IsPlanarEmbedding v) :
      IsPlanarEmbedding (fun theta => G (v theta)) := by
    refine ⟨G.contMDiff.comp hv.1, G.injective.comp hv.2.1, ?_⟩
    intro theta
    change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E2) ((G : E2 → E2) ∘ v) theta)
    rw [mfderiv_comp theta (G.mdifferentiable (by simp) (v theta))
      (hv.1.mdifferentiable (by simp) theta)]
    exact ((G.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
      (x := v theta) (mem_univ _)).comp (hv.2.2 theta)
  have hC (i : Fin 2) :
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : ℝ × UnitCircle => C i p.1 p.2) ∧
      ∀ z : ℝ, IsPlanarEmbedding (C i z) ∧ range (C i z) = (B z i).boundary := by
    refine ⟨?_, fun z => ⟨hmapEmbedding (T z) (c0 i) (hc0 i), ?_⟩⟩
    · exact hTs.contMDiff.comp
        (contMDiff_fst.prodMk_space ((hc0 i).1.comp contMDiff_snd))
    · change range (fun theta => T z (c0 i theta)) =
        ((B0 i).mapDiffeomorph (T z)).boundary
      rw [BallNeighborhoodChart.mapDiffeomorph_boundary, ← hc0range i]
      exact range_comp' (T z) (c0 i)
  have hB (z : ℝ) :
      (B z 0).closedRegion ⊆ (B z 1).inside ∧ Disjoint (B z 0).boundary (B z 1).boundary := by
    constructor
    · change ((B0 0).mapDiffeomorph (T z)).closedRegion ⊆
        ((B0 1).mapDiffeomorph (T z)).inside
      rw [BallNeighborhoodChart.mapDiffeomorph_closedRegion,
        BallNeighborhoodChart.mapDiffeomorph_inside]
      exact image_mono hnest0
    · change Disjoint ((B0 0).mapDiffeomorph (T z)).boundary
        ((B0 1).mapDiffeomorph (T z)).boundary
      rw [BallNeighborhoodChart.mapDiffeomorph_boundary,
        BallNeighborhoodChart.mapDiffeomorph_boundary]
      exact disjoint_image_of_injective (T z).injective hdis0
  have hTlevel (z : ℝ) (hz : z ∈ Ioo (m - eta) (m + eta)) (x : E2) :
      heightCoordinates.symm (T z x, z) ∈ range j ↔
        heightCoordinates.symm (x, h0) ∈ range j := by
    have hl : h0 ∈ Ioo (m - eta) (m + eta) := hI ⟨le_rfl, hab⟩
    have hh := (hPhiLevel z hz ((Phi h0).symm x)).trans
      (hPhiLevel h0 hl ((Phi h0).symm x)).symm
    change heightCoordinates.symm (Phi z ((Phi h0).symm x), z) ∈ range j ↔
      heightCoordinates.symm (Phi h0 ((Phi h0).symm x), h0) ∈ range j at hh
    change heightCoordinates.symm (Phi z ((Phi h0).symm x), z) ∈ range j ↔
      heightCoordinates.symm (x, h0) ∈ range j
    simpa only [Diffeomorph.apply_symm_apply] using hh
  have hlevels (z : ℝ) (hz : z ∈ Ioo (m - eta) (m + eta)) :
      {x : E2 | heightCoordinates.symm (x, z) ∈ range j} =
        ⋃ i : Fin 2, (B z i).boundary := by
    ext x
    constructor
    · intro hx
      change heightCoordinates.symm (x, z) ∈ range j at hx
      have hx0 : heightCoordinates.symm ((T z).symm x, h0) ∈ range j := by
        apply (hTlevel z hz ((T z).symm x)).mp
        simpa only [Diffeomorph.apply_symm_apply] using hx
      have hx0' : (T z).symm x ∈ ⋃ i : Fin 2, (B0 i).boundary := by
        rw [← hlevel0]
        exact hx0
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx0'
      refine mem_iUnion.mpr ⟨i, ?_⟩
      change x ∈ ((B0 i).mapDiffeomorph (T z)).boundary
      rw [BallNeighborhoodChart.mapDiffeomorph_boundary]
      exact ⟨(T z).symm x, hi, (T z).apply_symm_apply x⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      change x ∈ ((B0 i).mapDiffeomorph (T z)).boundary at hi
      rw [BallNeighborhoodChart.mapDiffeomorph_boundary] at hi
      rcases hi with ⟨y, hy, rfl⟩
      apply (hTlevel z hz y).mpr
      change y ∈ {x : E2 | heightCoordinates.symm (x, h0) ∈ range j}
      rw [hlevel0]
      exact mem_iUnion.mpr ⟨i, hy⟩
  let pi : E3 → E2 := fun y => (heightCoordinates y).1
  let ca : Fin 2 → UnitCircle → E3 := fun i theta =>
    heightCoordinates.symm (C i b theta, b)
  have hemb (i : Fin 2) : IsPlanarEmbedding (C i b) := ((hC i).2 b).1
  have hCa : {x : E2 | heightCoordinates.symm (x, b) ∈ range j} =
      ⋃ i : Fin 2, range (C i b) := by
    rw [hlevels b (hI ⟨hab, le_rfl⟩)]
    exact iUnion_congr (fun i => ((hC i).2 b).2.symm)
  have hCadis : Disjoint (range (C 0 b)) (range (C 1 b)) := by
    rw [((hC 0).2 b).2, ((hC 1).2 b).2]
    exact (hB b).2
  have hcaproj (i : Fin 2) : pi ∘ ca i = C i b := by
    funext theta
    change (heightCoordinates (heightCoordinates.symm (C i b theta, b))).1 = _
    rw [heightCoordinates.apply_symm_apply]
  have hcaproj_apply (i : Fin 2) (theta : UnitCircle) : pi (ca i theta) = C i b theta :=
    congrFun (hcaproj i) theta
  have hlift (i : Fin 2) : ∃ q : UnitCircle → UnitTwoSphere,
      ContMDiff (𝓡 1) (𝓡 2) ∞ q ∧ Injective q ∧
      (∀ theta, Injective (mfderiv (𝓡 1) (𝓡 2) q theta)) ∧
      ∀ theta, j (q theta) = ca i theta := by
    have hcs : ContMDiff (𝓡 1) 𝓘(ℝ, E3) ∞ (ca i) :=
      heightCoordinates.symm.contDiff.contMDiff.comp
        ((hemb i).1.prodMk_space contMDiff_const)
    have hci : Injective (ca i) := by
      intro s t hst
      apply (hemb i).2.1
      simpa only [hcaproj_apply] using congrArg pi hst
    have hcd (theta : UnitCircle) :
        Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3) (ca i) theta) := by
      have hpim : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E2) ∞ pi :=
        (contDiff_fst.comp heightCoordinates.contDiff).contMDiff
      have hh := (hpim.mdifferentiable (by simp) (ca i theta)).hasMFDerivAt.comp
        theta (hcs.mdifferentiable (by simp) theta).hasMFDerivAt
      rw [hcaproj] at hh
      intro x y hxy
      apply (hemb i).2.2 theta
      rw [hh.mfderiv]
      exact congrArg (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E2) pi (ca i theta)) hxy
    have hcentral : range (ca i) ⊆ range (fun p : UnitTwoSphere => psi (p, 0)) := by
      rw [hpsi0]
      rintro y ⟨theta, rfl⟩
      have ht : C i b theta ∈ ⋃ l : Fin 2, range (C l b) :=
        mem_iUnion.mpr ⟨i, ⟨theta, rfl⟩⟩
      rw [← hCa] at ht
      exact ht
    obtain ⟨q, hqs, hqi, hqd, hqr⟩ :=
      exists_collar_circle_source_pullback psi hpsi (ca i) hcs hci hcd hcentral
    refine ⟨q, hqs, hqi, hqd, ?_⟩
    intro theta
    rw [← congrFun hpsi0 (q theta)]
    exact hqr theta
  choose q hqs hqi hqd hqr using hlift
  have hq (i : Fin 2) : ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Injective (q i) ∧
      ∀ theta, Injective (mfderiv (𝓡 1) (𝓡 2) (q i) theta) :=
    ⟨hqs i, hqi i, hqd i⟩
  have hqdis : Disjoint (range (q 0)) (range (q 1)) := by
    apply disjoint_left.mpr
    rintro x ⟨s, rfl⟩ ⟨t, ht⟩
    have hh : C 1 b t = C 0 b s := by
      have hjj := congrArg j ht
      rw [hqr 1 t, hqr 0 s] at hjj
      simpa only [hcaproj_apply] using congrArg pi hjj
    exact disjoint_left.mp hCadis ⟨s, rfl⟩ ⟨t, hh⟩
  have hqpair (i l : Fin 2) (hil : i ≠ l) : Disjoint (range (q i)) (range (q l)) := by
    fin_cases i <;> fin_cases l <;>
      first | exact False.elim (hil rfl) | exact hqdis | exact hqdis.symm
  have hqlevel : (⋃ i : Fin 2, range (q i)) = {p : UnitTwoSphere | H p = b} := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, theta, rfl⟩ := mem_iUnion.mp hx
      change (heightCoordinates (j (q i theta))).2 = b
      rw [hqr]
      exact congrArg Prod.snd (heightCoordinates.apply_symm_apply (C i b theta, b))
    · intro hx
      change (heightCoordinates (j x)).2 = b at hx
      have hrec : heightCoordinates.symm (pi (j x), b) = j x := by
        apply heightCoordinates.injective
        rw [heightCoordinates.apply_symm_apply]
        exact Prod.ext rfl hx.symm
      have hm : pi (j x) ∈ ⋃ i : Fin 2, range (C i b) := by
        rw [← hCa]
        change heightCoordinates.symm (pi (j x), b) ∈ range j
        rw [hrec]
        exact ⟨x, rfl⟩
      obtain ⟨i, theta, ht⟩ := mem_iUnion.mp hm
      refine mem_iUnion.mpr ⟨i, ⟨theta, hji ?_⟩⟩
      rw [hqr]
      change heightCoordinates.symm (C i b theta, b) = j x
      rw [ht, hrec]
  exact ⟨B0, T, eta, q, hB0, hnest0, hclosed, hinside, hreg,
    heta, hI, hTs, hTi, hT0, hC, hB, hTlevel, hlevels, hq, hqpair, hqlevel, hqr⟩

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
