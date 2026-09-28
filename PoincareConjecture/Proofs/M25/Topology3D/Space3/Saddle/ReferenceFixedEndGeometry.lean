import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceLowerFixedEnd
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceUpperFixedEnd
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ContainedProfileBall
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightTubeTransport
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic









set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D



theorem exists_nonnested_reference_fixed_end_geometry
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hdZero : ∀ q : ℝ, sigma ≤ q → d q = 0)
    (hdBounds : ∀ q : ℝ, 0 ≤ q → -q ^ 2 / 2 ≤ d q ∧ d q ≤ 0)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (u : UnitTwoSphere) (P : SurgeryCapProfile) :
    let L := heightPlaneCoordinates u
    let F : E3 → E3 := fun y =>
      L.symm (J2.symm (nonnestedReferenceDiffeomorph 0 d hd y).1,
        (nonnestedReferenceDiffeomorph 0 d hd y).2)
    let j : UnitTwoSphere → E3 := fun q => F (q : E3)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let S := range j
    let cut : Fin 3 → ℝ := ![-1 / 8, -1 / 8, 3 / 2]
    let sign : Fin 3 → ℝ := ![1, 1, -1]
    let E : Fin 3 → Set E3 := ![
      j '' {q | 0 < (q : E3) 1 ∧ H (j q) ≤ -1 / 8},
      j '' {q | (q : E3) 1 < 0 ∧ H (j q) ≤ -1 / 8},
      j '' {q | 3 / 2 ≤ H (j q)}]
    let R := S ∩ {y | -1 / 8 ≤ H y ∧ H y ≤ 3 / 2}
    let sector : Fin 3 → Set E3 := ![
      {y | 0 < (J2 (L y).1).2}, {y | (J2 (L y).1).2 < 0}, univ]
    let M := flatCapDiffeomorph P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
    ∃ T : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3,
      (∀ i : Fin 3,
        closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T i).source ∧
        ContDiffOn ℝ ∞ (T i) (T i).source ∧
        ContDiffOn ℝ ∞ (T i).symm (T i).target ∧
        (∀ p ∈ (T i).source, H (T i p) = p.2) ∧
        (∀ y ∈ (T i).target, ((T i).symm y).2 = H y) ∧
        ∀ z : ℝ, |z - cut i| < 1 / 128 →
          T i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
            S ∩ {y | H y = z} ∩ sector i) ∧
      ∀ lambda : Fin 3 → ℝ, (∀ i, 0 < lambda i) →
        (∀ i, lambda i * P.heightBound < 1 / 256) →
        ∃ (A N : Fin 3 → BallNeighborhoodChart E3 E3) (o : Fin 3 → ℝ),
          let cap : Fin 3 → E3 → E3 := fun i y =>
            T i ((M (heightCoordinates y)).1,
              cut i + sign i * lambda i * (M (heightCoordinates y)).2)
          let north : Fin 3 → Set E3 := fun i => cap i ''
            {y | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}
          let south : Fin 3 → Set E3 := fun i => cap i ''
            {y | ‖y‖ = 1 ∧ (heightCoordinates y).2 ≤ 0}
          (∀ i : Fin 3,
            (A i).boundary = E i ∪ north i ∧
            (A i).closedRegion ⊆ F '' closedBall (0 : E3) 1 ∧
            Disjoint (A i).inside S ∧
            (A i).closedRegion ∩ R ⊆ north i ∧
            E i ∩ north i = T i '' (sphere (0 : E2) 1 ×ˢ ({cut i} : Set ℝ)) ∧
            (∀ s ∈ Icc (0 : ℝ) (1 / 128),
              let z := cut i - sign i * s
              (A i).inside ∩ {y | H y = z} =
                T i '' (ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) ∧
              (A i).closedRegion ∩ {y | H y = z} =
                T i '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ))) ∧
            (N i).boundary = south i ∪ north i ∧
            (N i).chart.source = {y : E3 |
              ((M (heightCoordinates y)).1,
                cut i + sign i * lambda i * (M (heightCoordinates y)).2) ∈ (T i).source} ∧
            (N i).chart.target = (T i).target ∧
            (∀ y : E3, (N i).chart y = cap i y) ∧
            (∀ y : E3, (N i).chart.symm y = heightCoordinates.symm
              (M.symm (((T i).symm y).1,
                (((T i).symm y).2 - cut i) / (sign i * lambda i)))) ∧
            (N i).closedRegion ⊆ (A i).closedRegion ∧
            (N i).closedRegion ⊆ {y | |H y - cut i| ≤ lambda i * P.heightBound} ∧
            0 < o i ∧ o i < 1 / 4 ∧
            (∀ q : UnitTwoSphere, -o i < (heightCoordinates (q : E3)).2 →
              (N i).chart (q : E3) ∈ (A i).boundary)) ∧
          (∀ i k : Fin 3, i ≠ k → Disjoint (A i).closedRegion (A k).closedRegion) ∧
          S = R ∪ (⋃ i : Fin 3, E i) := by
  classical
  dsimp only
  let L := heightPlaneCoordinates u
  let W := (J2.symm.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).toDiffeomorph.trans
    L.symm.toDiffeomorph
  let F := (nonnestedReferenceDiffeomorph 0 d hd).trans W
  let j : UnitTwoSphere → E3 := fun q => F (q : E3)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let S := range j
  let cut : Fin 3 → ℝ := ![-1 / 8, -1 / 8, 3 / 2]
  let sign : Fin 3 → ℝ := ![1, 1, -1]
  let E : Fin 3 → Set E3 := ![
    j '' {q | 0 < (q : E3) 1 ∧ H (j q) ≤ -1 / 8},
    j '' {q | (q : E3) 1 < 0 ∧ H (j q) ≤ -1 / 8},
    j '' {q | 3 / 2 ≤ H (j q)}]
  let R := S ∩ {y | -1 / 8 ≤ H y ∧ H y ≤ 3 / 2}
  let sector : Fin 3 → Set E3 := ![
    {y | 0 < (J2 (L y).1).2}, {y | (J2 (L y).1).2 < 0}, univ]
  let M := flatCapDiffeomorph P.horizontal P.vertical
    P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
  obtain ⟨_, T0, _, _, _, _, _, _, _, hT0s, hT0, hT0i, hT0h, hT0ih,
    hC0, hEnd0⟩ := exists_nonnested_reference_lower_fixed_end
      sigma hsigma hsigmaSmall d hd hdZero hdBounds J2 hJ2 u P 0
  obtain ⟨_, T1, _, _, _, _, _, _, _, hT1s, hT1, hT1i, hT1h, hT1ih,
    hC1, hEnd1⟩ := exists_nonnested_reference_lower_fixed_end
      sigma hsigma hsigmaSmall d hd hdZero hdBounds J2 hJ2 u P 1
  obtain ⟨_, T2, _, _, _, _, _, _, _, hT2s, hT2, hT2i, hT2h, hT2ih,
    hC2, hEnd2⟩ := exists_nonnested_reference_upper_fixed_end
      sigma hsigma hsigmaSmall d hd hdZero hdBounds J2 hJ2 u P
  let T : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3 := ![T0, T1, T2]
  have hTube (i : Fin 3) :
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T i).source ∧
      ContDiffOn ℝ ∞ (T i) (T i).source ∧
      ContDiffOn ℝ ∞ (T i).symm (T i).target ∧
      (∀ p ∈ (T i).source, H (T i p) = p.2) ∧
      (∀ y ∈ (T i).target, ((T i).symm y).2 = H y) ∧
      ∀ z : ℝ, |z - cut i| < 1 / 128 →
        T i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
          S ∩ {y | H y = z} ∩ sector i := by
    fin_cases i
    · refine ⟨hT0s, hT0, hT0i, hT0h, hT0ih, ?_⟩
      intro z hz
      have hz0 : |z + 1 / 8| < 1 / 128 := by
        norm_num [cut, sub_eq_add_neg] at hz ⊢
        simpa [add_comm] using hz
      simpa [T, S, H, j, F, W, L, sector] using hC0 z hz0
    · refine ⟨hT1s, hT1, hT1i, hT1h, hT1ih, ?_⟩
      intro z hz
      have hz1 : |z + 1 / 8| < 1 / 128 := by
        norm_num [cut, sub_eq_add_neg] at hz ⊢
        simpa [add_comm] using hz
      simpa [T, S, H, j, F, W, L, sector] using hC1 z hz1
    · refine ⟨hT2s, hT2, hT2i, hT2h, hT2ih, ?_⟩
      intro z hz
      simpa [T, S, H, j, F, W, L, sector] using hC2 z hz
  refine ⟨T, hTube, ?_⟩
  intro lambda hlambda hsmall
  let cap : Fin 3 → E3 → E3 := fun i y => T i ((M (heightCoordinates y)).1,
    cut i + sign i * lambda i * (M (heightCoordinates y)).2)
  let north : Fin 3 → Set E3 := fun i => cap i ''
    {y | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}
  let south : Fin 3 → Set E3 := fun i => cap i ''
    {y | ‖y‖ = 1 ∧ (heightCoordinates y).2 ≤ 0}
  obtain ⟨A0, hA0b, hA0c, hA0s, hA0h, hA0cut, hA0patch⟩ :=
    hEnd0 (lambda 0) (hlambda 0) (hsmall 0)
  obtain ⟨A1, hA1b, hA1c, hA1s, hA1h, hA1cut, hA1patch⟩ :=
    hEnd1 (lambda 1) (hlambda 1) (hsmall 1)
  obtain ⟨A2, hA2b, hA2c, hA2h, hA2cut, hA2patch⟩ :=
    hEnd2 (lambda 2) (hlambda 2) (hsmall 2)
  let A : Fin 3 → BallNeighborhoodChart E3 E3 := ![A0, A1, A2]
  have hA (i : Fin 3) :
      (A i).boundary = E i ∪ north i ∧
      (A i).closedRegion ⊆ F '' closedBall (0 : E3) 1 ∧
      (∀ s ∈ Icc (0 : ℝ) (1 / 128),
        let z := cut i - sign i * s
        (A i).inside ∩ {y | H y = z} =
          T i '' (ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) ∧
        (A i).closedRegion ∩ {y | H y = z} =
          T i '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ))) ∧
      ∀ q : UnitTwoSphere, -1 / 8 < (heightCoordinates (q : E3)).2 →
        cap i (q : E3) ∈ (A i).boundary := by
    have hA0cut' : ∀ s ∈ Icc (0 : ℝ) (1 / 128),
        let z := cut 0 - sign 0 * s
        A0.inside ∩ {y | H y = z} = T 0 '' (ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) ∧
        A0.closedRegion ∩ {y | H y = z} = T 0 '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) := by
      intro s hs
      dsimp
      simpa [cut, sign, T, H, S, j, F, W, L] using hA0cut s hs
    have hA1cut' : ∀ s ∈ Icc (0 : ℝ) (1 / 128),
        let z := cut 1 - sign 1 * s
        A1.inside ∩ {y | H y = z} = T 1 '' (ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) ∧
        A1.closedRegion ∩ {y | H y = z} = T 1 '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) := by
      intro s hs
      dsimp
      simpa [cut, sign, T, H, S, j, F, W, L] using hA1cut s hs
    have hA2cut' : ∀ s ∈ Icc (0 : ℝ) (1 / 128),
        let z := cut 2 - sign 2 * s
        A2.inside ∩ {y | H y = z} = T 2 '' (ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) ∧
        A2.closedRegion ∩ {y | H y = z} = T 2 '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ)) := by
      intro s hs
      dsimp
      simpa [cut, sign, T, H, S, j, F, W, L, sub_eq_add_neg] using hA2cut s hs
    have hA0cut'' : ∀ s : ℝ, 0 ≤ s → s ≤ (128 : ℝ)⁻¹ →
        A0.inside ∩ {y | H y = -1 / 8 + -s} = T0 '' (ball (0 : E2) 1 ×ˢ ({-1 / 8 + -s} : Set ℝ)) ∧
        A0.closedRegion ∩ {y | H y = -1 / 8 + -s} =
          T0 '' (closedBall (0 : E2) 1 ×ˢ ({-1 / 8 + -s} : Set ℝ)) := by
      intro s hs0 hs1
      have hs1' : s ≤ 1 / 128 := by
        norm_num at hs1 ⊢
        exact hs1
      have h := hA0cut' s ⟨hs0, hs1'⟩
      simpa [cut, sign, T, sub_eq_add_neg] using h
    have hA1cut'' : ∀ s : ℝ, 0 ≤ s → s ≤ (128 : ℝ)⁻¹ →
        A1.inside ∩ {y | H y = -1 / 8 + -s} = T1 '' (ball (0 : E2) 1 ×ˢ ({-1 / 8 + -s} : Set ℝ)) ∧
        A1.closedRegion ∩ {y | H y = -1 / 8 + -s} =
          T1 '' (closedBall (0 : E2) 1 ×ˢ ({-1 / 8 + -s} : Set ℝ)) := by
      intro s hs0 hs1
      have hs1' : s ≤ 1 / 128 := by
        norm_num at hs1 ⊢
        exact hs1
      have h := hA1cut' s ⟨hs0, hs1'⟩
      simpa [cut, sign, T, sub_eq_add_neg] using h
    have hA2cut'' : ∀ s : ℝ, 0 ≤ s → s ≤ (128 : ℝ)⁻¹ →
        A2.inside ∩ {y | H y = 3 / 2 + s} = T2 '' (ball (0 : E2) 1 ×ˢ ({3 / 2 + s} : Set ℝ)) ∧
        A2.closedRegion ∩ {y | H y = 3 / 2 + s} =
          T2 '' (closedBall (0 : E2) 1 ×ˢ ({3 / 2 + s} : Set ℝ)) := by
      intro s hs0 hs1
      have hs1' : s ≤ 1 / 128 := by
        norm_num at hs1 ⊢
        exact hs1
      have h := hA2cut' s ⟨hs0, hs1'⟩
      simpa [cut, sign, T, sub_eq_add_neg] using h
    have hA0patch' : ∀ a : E3, ‖a‖ = 1 → -1 / 8 < (heightCoordinates a).2 →
        T0 ((M (heightCoordinates a)).1,
          -1 / 8 + lambda 0 * (M (heightCoordinates a)).2) ∈ A0.boundary := by
      intro a ha hh
      let q : UnitTwoSphere := ⟨a, mem_sphere_zero_iff_norm.mpr ha⟩
      have hq := hA0patch q (by simpa [q] using hh)
      simpa [q, M] using hq
    have hA1patch' : ∀ a : E3, ‖a‖ = 1 → -1 / 8 < (heightCoordinates a).2 →
        T1 ((M (heightCoordinates a)).1,
          -1 / 8 + lambda 1 * (M (heightCoordinates a)).2) ∈ A1.boundary := by
      intro a ha hh
      let q : UnitTwoSphere := ⟨a, mem_sphere_zero_iff_norm.mpr ha⟩
      have hq := hA1patch q (by simpa [q] using hh)
      simpa [q, M] using hq
    have hA2patch' : ∀ a : E3, ‖a‖ = 1 → -1 / 8 < (heightCoordinates a).2 →
        T2 ((M (heightCoordinates a)).1,
          3 / 2 + -(lambda 2 * (M (heightCoordinates a)).2)) ∈ A2.boundary := by
      intro a ha hh
      let q : UnitTwoSphere := ⟨a, mem_sphere_zero_iff_norm.mpr ha⟩
      have hq := hA2patch q (by simpa [q] using hh)
      simpa [q, M, sub_eq_add_neg] using hq
    fin_cases i
    · simpa [A, E, T, cut, sign, cap, north, sub_eq_add_neg, j, F, W, L, H, M] using
        And.intro hA0b ⟨hA0c, hA0cut'', hA0patch'⟩
    · simpa [A, E, T, cut, sign, cap, north, sub_eq_add_neg, j, F, W, L, H, M] using
        And.intro hA1b ⟨hA1c, hA1cut'', hA1patch'⟩
    · simpa [A, E, T, cut, sign, cap, north, sub_eq_add_neg, j, F, W, L, H, M] using
        And.intro hA2b ⟨hA2c, hA2cut'', hA2patch'⟩
  have hImage (i : Fin 3) (Q : E3 → Prop) :
      (fun q : UnitTwoSphere => cap i (q : E3)) '' {q | Q (q : E3)} =
        cap i '' {y | ‖y‖ = 1 ∧ Q y} := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(q : E3), ⟨norm_eq_of_mem_sphere q, hq⟩, rfl⟩
    · rintro ⟨q, ⟨hqn, hq⟩, rfl⟩
      exact ⟨⟨q, mem_sphere_zero_iff_norm.mpr hqn⟩, hq, rfl⟩
  let GoodN (i : Fin 3) (N : BallNeighborhoodChart E3 E3) : Prop :=
    N.boundary = south i ∪ north i ∧
    N.chart.source = {y : E3 | ((M (heightCoordinates y)).1,
      cut i + sign i * lambda i * (M (heightCoordinates y)).2) ∈ (T i).source} ∧
    N.chart.target = (T i).target ∧
    (∀ y : E3, N.chart y = cap i y) ∧
    (∀ y : E3, N.chart.symm y = heightCoordinates.symm
      (M.symm (((T i).symm y).1, (((T i).symm y).2 - cut i) / (sign i * lambda i)))) ∧
    N.closedRegion ⊆ (A i).closedRegion ∧
    south i ∩ north i = T i '' (sphere (0 : E2) 1 ×ˢ ({cut i} : Set ℝ))
  have hLowerN (i : Fin 3) (hsi : sign i = 1) : ∃ N, GoodN i N := by
    rcases hTube i with ⟨hTs, hT, hTi, hTh, _, _⟩
    have hProfile (Q : E3 → Prop) :
        (fun q : UnitTwoSphere => T i ((P.model q).1,
          cut i + lambda i * (P.model q).2)) '' {q | Q (q : E3)} =
            cap i '' {y | ‖y‖ = 1 ∧ Q y} := by
      rw [← hImage i Q]
      apply image_congr
      intro q _
      change T i ((P.model q).1, cut i + lambda i * (P.model q).2) =
        T i ((P.model q).1, cut i + sign i * lambda i * (P.model q).2)
      rw [hsi, one_mul]
    have hFilled (t : ℝ) (ht : t ∈ Icc (cut i - 1 / 128) (cut i)) :
        T i '' (closedBall (0 : E2) 1 ×ˢ ({t} : Set ℝ)) ⊆ (A i).closedRegion := by
      have hs : cut i - t ∈ Icc (0 : ℝ) (1 / 128) := by
        constructor <;> linarith [ht.1, ht.2]
      have hh := ((hA i).2.2.1 (cut i - t) hs).2
      have he : cut i - sign i * (cut i - t) = t := by rw [hsi]; ring
      rw [he] at hh
      exact fun _ hy => (hh.symm ▸ hy).1
    have hNorth : (fun q : UnitTwoSphere => T i ((P.model q).1,
        cut i + lambda i * (P.model q).2)) ''
          {q | 0 ≤ (heightCoordinates (q : E3)).2} ⊆ (A i).closedRegion := by
      have hProfileN := hProfile (fun y : E3 => 0 ≤ (heightCoordinates y).2)
      rw [hProfileN]
      intro y hy
      rw [← (A i).inside_union_boundary, (hA i).1]
      exact Or.inr (Or.inr hy)
    obtain ⟨N, hNb, hNs, hNt, hNp, hNi, hNc, _, _, hNrim⟩ :=
      exists_saddle_contained_profile_ball P u (T i) hTs hT hTi hTh (A i)
        (cut i - 1 / 128) (cut i) (lambda i) (1 / 128) (hlambda i)
        (by linarith [hsmall i]) (by linarith [hsmall i]) hFilled hNorth
    refine ⟨N, ?_⟩
    change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
    refine ⟨?_, ?_, hNt, ?_, ?_, hNc, ?_⟩
    · have hProfileS := hProfile (fun y : E3 => (heightCoordinates y).2 ≤ 0)
      have hProfileN := hProfile (fun y : E3 => 0 ≤ (heightCoordinates y).2)
      rw [hProfileS, hProfileN] at hNb
      simpa only [south, north] using hNb
    · simpa only [hsi, one_mul] using hNs
    · intro y
      simpa only [cap, hsi, one_mul] using hNp y
    · intro y
      simpa only [hsi, one_mul] using hNi y
    · have hProfileS := hProfile (fun y : E3 => (heightCoordinates y).2 ≤ 0)
      have hProfileN := hProfile (fun y : E3 => 0 ≤ (heightCoordinates y).2)
      rw [hProfileS, hProfileN] at hNrim
      simpa only [south, north] using hNrim
  have hUpperN : ∃ N, GoodN 2 N := by
    rcases hTube 2 with ⟨hTs, hT, hTi, hTh, _, _⟩
    let negD := (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).toDiffeomorph
    let idD := Diffeomorph.refl 𝓘(ℝ, E3) E3 ∞
    let Tm := heightTransportTube (T 2) negD idD
    let Hm : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 ((-u : UnitTwoSphere) : E3)
    have hHm (y : E3) : Hm y = -H y := by
      change ⟪((-u : UnitTwoSphere) : E3), y⟫_ℝ = -⟪(u : E3), y⟫_ℝ
      rw [coe_neg_sphere, inner_neg_left]
    have hTmp (p : E2 × ℝ) : Tm p = T 2 (p.1, -p.2) := rfl
    have hTmi (y : E3) : Tm.symm y = (((T 2).symm y).1, -((T 2).symm y).2) := rfl
    have hTmt : Tm.target = (T 2).target := by
      ext y
      exact heightTransportTube_mem_target (T 2) negD idD y
    have hTms : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ Tm.source :=
      heightTransportTube_closedDisc_source (T 2) negD idD hTs
    have hTm : ContDiffOn ℝ ∞ Tm Tm.source :=
      heightTransportTube_contDiffOn (T 2) negD idD hT
    have hTminv : ContDiffOn ℝ ∞ Tm.symm Tm.target :=
      heightTransportTube_contDiffOn_symm (T 2) negD idD hTi
    have hTmh (p : E2 × ℝ) (hp : p ∈ Tm.source) : Hm (Tm p) = p.2 := by
      have hps : (p.1, -p.2) ∈ (T 2).source :=
        (heightTransportTube_mem_source (T 2) negD idD p).mp hp
      rw [hHm, hTmp, hTh _ hps, neg_neg]
    have hTmSlice (X : Set E2) (t : ℝ) :
        Tm '' (X ×ˢ ({-t} : Set ℝ)) = T 2 '' (X ×ˢ ({t} : Set ℝ)) := by
      ext y
      constructor
      · rintro ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
        have hst : s = -t := hs
        subst s
        exact ⟨(x, t), ⟨hx, mem_singleton _⟩, by rw [hTmp]; simp only [neg_neg]⟩
      · rintro ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
        have hst : s = t := hs
        subst s
        exact ⟨(x, -t), ⟨hx, mem_singleton _⟩, by rw [hTmp]; simp only [neg_neg]⟩
    have hCap (y : E3) : Tm ((M (heightCoordinates y)).1,
        -cut 2 + lambda 2 * (M (heightCoordinates y)).2) = cap 2 y := by
      rw [hTmp]
      change T 2 (_, -(-cut 2 + lambda 2 * (M (heightCoordinates y)).2)) =
        T 2 (_, cut 2 + sign 2 * lambda 2 * (M (heightCoordinates y)).2)
      congr 1
      apply Prod.ext
      · rfl
      · change -(-cut 2 + lambda 2 * (M (heightCoordinates y)).2) =
          cut 2 + -1 * lambda 2 * (M (heightCoordinates y)).2
        ring
    have hProfile (Q : E3 → Prop) :
        (fun q : UnitTwoSphere => Tm ((P.model q).1,
          -cut 2 + lambda 2 * (P.model q).2)) '' {q | Q (q : E3)} =
            cap 2 '' {y | ‖y‖ = 1 ∧ Q y} := by
      rw [← hImage 2 Q]
      exact image_congr (fun q _ => hCap q)
    have hFilled (t : ℝ) (ht : t ∈ Icc (-cut 2 - 1 / 128) (-cut 2)) :
        Tm '' (closedBall (0 : E2) 1 ×ˢ ({t} : Set ℝ)) ⊆ (A 2).closedRegion := by
      have he : Tm '' (closedBall (0 : E2) 1 ×ˢ ({t} : Set ℝ)) =
          T 2 '' (closedBall (0 : E2) 1 ×ˢ ({-t} : Set ℝ)) := by
        simpa only [neg_neg] using hTmSlice (closedBall (0 : E2) 1) (-t)
      rw [he]
      have hs : -t - cut 2 ∈ Icc (0 : ℝ) (1 / 128) := by
        constructor <;> linarith [ht.1, ht.2]
      have hh := ((hA 2).2.2.1 (-t - cut 2) hs).2
      have hz : cut 2 - sign 2 * (-t - cut 2) = -t := by change _ - -1 * _ = _; ring
      rw [hz] at hh
      exact fun _ hy => (hh.symm ▸ hy).1
    have hNorth : (fun q : UnitTwoSphere => Tm ((P.model q).1,
        -cut 2 + lambda 2 * (P.model q).2)) ''
          {q | 0 ≤ (heightCoordinates (q : E3)).2} ⊆ (A 2).closedRegion := by
      have hProfileN := hProfile (fun y : E3 => 0 ≤ (heightCoordinates y).2)
      rw [hProfileN]
      intro y hy
      rw [← (A 2).inside_union_boundary, (hA 2).1]
      exact Or.inr (Or.inr hy)
    obtain ⟨N, hNb, hNs, hNt, hNp, hNi, hNc, _, _, hNrim⟩ :=
      exists_saddle_contained_profile_ball P (-u) Tm hTms hTm hTminv hTmh (A 2)
        (-cut 2 - 1 / 128) (-cut 2) (lambda 2) (1 / 128) (hlambda 2)
        (by linarith [hsmall 2]) (by linarith [hsmall 2]) hFilled hNorth
    refine ⟨N, ?_⟩
    change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
    refine ⟨?_, ?_, hNt.trans hTmt, fun y => (hNp y).trans (hCap y), ?_, hNc, ?_⟩
    · have hProfileS := hProfile (fun y : E3 => (heightCoordinates y).2 ≤ 0)
      have hProfileN := hProfile (fun y : E3 => 0 ≤ (heightCoordinates y).2)
      rw [hProfileS, hProfileN] at hNb
      simpa only [south, north] using hNb
    · rw [hNs]
      ext y
      simp only [Set.mem_ofPred_eq]
      dsimp only [Tm]
      rw [(heightTransportTube_mem_source (T 2) negD idD)]
      have hneg (x : ℝ) : negD.symm x = -x := by rfl
      rw [hneg]
      change ((M (heightCoordinates y)).1,
        -(-cut 2 + lambda 2 * (M (heightCoordinates y)).2)) ∈ (T 2).source ↔ _
      have he : -(-cut 2 + lambda 2 * (M (heightCoordinates y)).2) =
          cut 2 + sign 2 * lambda 2 * (M (heightCoordinates y)).2 := by
        change _ = cut 2 + -1 * lambda 2 * _
        ring
      rw [he]
    · intro y
      rw [hNi, hTmi]
      apply congrArg heightCoordinates.symm
      apply congrArg M.symm
      apply Prod.ext
      · rfl
      · change (-((T 2).symm y).2 - -cut 2) / lambda 2 =
          (((T 2).symm y).2 - cut 2) / (-1 * lambda 2)
        rw [neg_one_mul, div_neg]
        ring
    · have hProfileS := hProfile (fun y : E3 => (heightCoordinates y).2 ≤ 0)
      have hProfileN := hProfile (fun y : E3 => 0 ≤ (heightCoordinates y).2)
      rw [hProfileS, hProfileN] at hNrim
      simpa only [south, north, hTmSlice] using hNrim
  have hNexists (i : Fin 3) : ∃ N, GoodN i N := by
    fin_cases i
    · exact hLowerN 0 rfl
    · exact hLowerN 1 rfl
    · exact hUpperN
  choose N hN using hNexists
  let J := heightCoordinates.toDiffeomorph.trans M
  have hJhor (y : E3) (hy : y ∈ closedBall (0 : E3) 1) : ‖(J y).1‖ ≤ 1 := by
    apply flatCapDiffeomorph_fst_norm_le P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
      P.horizontal_pos P.horizontal_bound
    change ‖(heightCoordinates y).1‖ ^ 2 + (heightCoordinates y).2 ^ 2 ≤ 1
    rw [← heightCoordinates_norm_sq]
    have hy' := mem_closedBall_zero_iff.mp hy
    nlinarith [norm_nonneg y]

  have hJclosed : IsCompact (J '' closedBall (0 : E3) 1) :=
    (isCompact_closedBall (0 : E3) 1).image J.continuous
  have hJopen : IsOpen (J '' ball (0 : E3) 1) := J.toHomeomorph.isOpenMap _ isOpen_ball
  have hJne : (J '' closedBall (0 : E3) 1).Nonempty := ⟨J 0, 0, by simp, rfl⟩
  have hext (a : ℝ) (ha : |a| = 1) :
      ∀ p ∈ J '' closedBall (0 : E3) 1, a * p.2 ≤ P.heightBound := by
    obtain ⟨p, hp, hmax⟩ := hJclosed.exists_isMaxOn hJne
      (f := fun p : E2 × ℝ => a * p.2) (by fun_prop)
    obtain ⟨y, hy, rfl⟩ := hp
    have hyb : y ∈ sphere (0 : E3) 1 := by
      by_contra hyb
      have hyn : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
      have hyl : ‖y‖ < 1 := lt_of_le_of_ne hyn
        (fun heq => hyb (mem_sphere_zero_iff_norm.mpr heq))
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hJopen (J y)
        ⟨y, mem_ball_zero_iff.mpr hyl, rfl⟩
      let p' : E2 × ℝ := ((J y).1, (J y).2 + a * (r / 2))
      have hp' : p' ∈ J '' closedBall (0 : E3) 1 := by
        apply image_mono ball_subset_closedBall
        apply hsub
        change dist ((J y).1, (J y).2 + a * (r / 2)) ((J y).1, (J y).2) < r
        rw [dist_prod_same_left, Real.dist_eq,
          show (J y).2 + a * (r / 2) - (J y).2 = a * (r / 2) by ring,
          abs_mul, ha, one_mul, abs_of_pos (by positivity : 0 < r / 2)]
        linarith
      have hsquare : a ^ 2 = 1 := by nlinarith [sq_abs a]
      have hstep : a * p'.2 = a * (J y).2 + r / 2 := by
        dsimp [p']
        calc
          _ = a * (J y).2 + a ^ 2 * (r / 2) := by ring
          _ = _ := by rw [hsquare, one_mul]
      have hh : a * p'.2 ≤ a * (J y).2 := hmax hp'
      rw [hstep] at hh
      linarith
    have hbnd : |(J y).2| ≤ P.heightBound := P.height_bound ⟨y, hyb⟩
    have hsign : a * (J y).2 ≤ |(J y).2| := by
      calc
        _ ≤ |a * (J y).2| := le_abs_self _
        _ = _ := by rw [abs_mul, ha, one_mul]
    exact fun p hp => (hmax hp).trans (hsign.trans hbnd)
  have hJheight (y : E3) (hy : y ∈ closedBall (0 : E3) 1) :
      |(J y).2| ≤ P.heightBound := by
    have hm := hext (-1) (by norm_num) (J y) ⟨y, hy, rfl⟩
    have hp := hext 1 (by norm_num) (J y) ⟨y, hy, rfl⟩
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsignAbs (i : Fin 3) : |sign i| = 1 := by fin_cases i <;> norm_num [sign]
  have hsignNe (i : Fin 3) : sign i ≠ 0 := by fin_cases i <;> norm_num [sign]
  have hNheight (i : Fin 3) :
      (N i).closedRegion ⊆ {y | |H y - cut i| ≤ lambda i * P.heightBound} := by
    rcases hN i with ⟨_, _, _, hNp, _, _, _⟩
    rintro y ⟨v, hv, rfl⟩
    have hvs : ((J v).1, cut i + sign i * lambda i * (J v).2) ∈ (T i).source :=
      (hTube i).1 ⟨mem_closedBall_zero_iff.mpr (hJhor v hv), mem_univ _⟩
    change |H ((N i).chart v) - cut i| ≤ lambda i * P.heightBound
    rw [hNp]
    change |H (T i ((J v).1, cut i + sign i * lambda i * (J v).2)) - cut i| ≤ _
    rw [(hTube i).2.2.2.1 _ hvs, add_sub_cancel_left]
    simp only [abs_mul, hsignAbs, one_mul, abs_of_pos (hlambda i)]
    exact mul_le_mul_of_nonneg_left (hJheight v hv) (hlambda i).le
  have hAvoid (i : Fin 3) : Disjoint (A i).inside S := by
    apply disjoint_left.mpr
    rintro y hyA ⟨q, rfl⟩
    have ho : IsOpen (F ⁻¹' (A i).inside) := (A i).inside_open.preimage F.continuous
    have hsub : F ⁻¹' (A i).inside ⊆ closedBall (0 : E3) 1 := by
      intro x hx
      have hclosed : F x ∈ (A i).closedRegion := by
        rw [← (A i).inside_union_boundary]
        exact Or.inl hx
      obtain ⟨z, hz, he⟩ := (hA i).2.1 hclosed
      have hzx : z = x := F.injective he
      simpa [hzx] using hz
    have hqi : (q : E3) ∈ interior (closedBall (0 : E3) 1) :=
      ho.subset_interior_iff.mpr hsub hyA
    rw [interior_closedBall (0 : E3) one_ne_zero] at hqi
    have hh := mem_ball_zero_iff.mp hqi
    rw [norm_eq_of_mem_sphere q] at hh
    exact (lt_irrefl 1) hh
  have hH (y : E3) : (L y).2 = H y := heightPlaneCoordinates_snd u y
  have hHs (p : E2 × ℝ) : H (L.symm p) = p.2 := by rw [← hH, L.apply_symm_apply]
  have hjh (q : UnitTwoSphere) : H (j q) =
      1 + (q : E3) 2 - (q : E3) 1 ^ 2 + d ((q : E3) 0 ^ 2 + (q : E3) 1 ^ 2) := by
    change H (L.symm (J2.symm (nonnestedReferenceDiffeomorph 0 d hd q).1,
      (nonnestedReferenceDiffeomorph 0 d hd q).2)) = _
    rw [hHs, (nonnestedReferenceDiffeomorph_apply_symm 0 d hd).1]
    simp only [zero_add]
  have hjp (q : UnitTwoSphere) :
      J2 (L (j q)).1 = ((q : E3) 0 / Real.sqrt 2, (q : E3) 1 / Real.sqrt 2) := by
    change J2 (L (L.symm (J2.symm (nonnestedReferenceDiffeomorph 0 d hd q).1,
      (nonnestedReferenceDiffeomorph 0 d hd q).2))).1 = _
    rw [L.apply_symm_apply, J2.apply_symm_apply,
      (nonnestedReferenceDiffeomorph_apply_symm 0 d hd).1]
  have htwo : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs0 (q : UnitTwoSphere) : j q ∈ sector 0 ↔ 0 < (q : E3) 1 := by
    change 0 < (J2 (L (j q)).1).2 ↔ _
    rw [hjp]
    exact div_pos_iff_of_pos_right htwo
  have hs1 (q : UnitTwoSphere) : j q ∈ sector 1 ↔ (q : E3) 1 < 0 := by
    change (J2 (L (j q)).1).2 < 0 ↔ _
    rw [hjp]
    rw [div_neg_iff]
    simp [htwo]
  have hEshape (i : Fin 3) :
      E i = S ∩ {y | sign i * (H y - cut i) ≤ 0} ∩ sector i := by
    fin_cases i
    · ext y
      constructor
      · rintro ⟨q, ⟨hq, hh⟩, rfl⟩
        refine ⟨⟨⟨q, rfl⟩, ?_⟩, (hs0 q).2 hq⟩
        change 1 * (H (j q) - -1 / 8) ≤ 0
        linarith
      · rintro ⟨⟨⟨q, rfl⟩, hh⟩, hq⟩
        refine ⟨q, ⟨(hs0 q).1 hq, ?_⟩, rfl⟩
        change 1 * (H (j q) - -1 / 8) ≤ 0 at hh
        linarith
    · ext y
      constructor
      · rintro ⟨q, ⟨hq, hh⟩, rfl⟩
        refine ⟨⟨⟨q, rfl⟩, ?_⟩, (hs1 q).2 hq⟩
        change 1 * (H (j q) - -1 / 8) ≤ 0
        linarith
      · rintro ⟨⟨⟨q, rfl⟩, hh⟩, hq⟩
        refine ⟨q, ⟨(hs1 q).1 hq, ?_⟩, rfl⟩
        change 1 * (H (j q) - -1 / 8) ≤ 0 at hh
        linarith
    · ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        refine ⟨⟨⟨q, rfl⟩, ?_⟩, mem_univ _⟩
        change -1 * (H (j q) - 3 / 2) ≤ 0
        norm_num at hq ⊢
        linarith
      · rintro ⟨⟨⟨q, rfl⟩, hq⟩, _⟩
        refine ⟨q, ?_, rfl⟩
        change -1 * (H (j q) - 3 / 2) ≤ 0 at hq
        change 3 / 2 ≤ H (j q)
        linarith
  have hEcut (i : Fin 3) : E i ∩ {y | H y = cut i} =
      T i '' (sphere (0 : E2) 1 ×ˢ ({cut i} : Set ℝ)) := by
    rw [hEshape]
    have hcircle := (hTube i).2.2.2.2.2 (cut i) (by norm_num)
    ext y
    constructor
    · rintro ⟨⟨⟨hyS, _⟩, hySector⟩, hyH⟩
      exact hcircle.symm ▸ ⟨⟨hyS, hyH⟩, hySector⟩
    · intro hy
      have hy' : y ∈ S ∩ {y | H y = cut i} ∩ sector i := hcircle ▸ hy
      have hside : sign i * (H y - cut i) ≤ 0 := by
        rw [hy'.1.2, sub_self, mul_zero]
      exact ⟨⟨⟨hy'.1.1, hside⟩, hy'.2⟩, hy'.1.2⟩
  have hNorthSide (i : Fin 3) (y : E3) (hy : y ∈ north i) :
      0 ≤ sign i * (H y - cut i) := by
    obtain ⟨q, ⟨hqn, hqh⟩, rfl⟩ := hy
    let q0 : UnitTwoSphere := ⟨q, mem_sphere_zero_iff_norm.mpr hqn⟩
    have hp : ((P.model q0).1, cut i + sign i * lambda i * (P.model q0).2) ∈
        (T i).source := (hTube i).1
      ⟨mem_closedBall_zero_iff.mpr (P.model_fst_norm_le q0), mem_univ _⟩
    have hm : 0 ≤ (P.model q0).2 := by
      change 0 ≤ P.vertical _ * (heightCoordinates q).2
      exact mul_nonneg (P.vertical_pos _).le hqh
    change 0 ≤ sign i * (H (T i ((P.model q0).1,
      cut i + sign i * lambda i * (P.model q0).2)) - cut i)
    rw [(hTube i).2.2.2.1 _ hp]
    have hsquare : sign i ^ 2 = 1 := by fin_cases i <;> norm_num [sign]
    have he : sign i * (cut i + sign i * lambda i * (P.model q0).2 - cut i) =
        lambda i * (P.model q0).2 := by
      calc
        _ = sign i ^ 2 * (lambda i * (P.model q0).2) := by ring
        _ = _ := by rw [hsquare, one_mul]
    rw [he]
    exact mul_nonneg (hlambda i).le hm
  have hRimNorth (i : Fin 3) :
      T i '' (sphere (0 : E2) 1 ×ˢ ({cut i} : Set ℝ)) ⊆ north i := by
    rcases hN i with ⟨_, _, _, _, _, _, hRim⟩
    exact fun _ hy => (hRim.symm ▸ hy).2
  have hRim (i : Fin 3) : E i ∩ north i =
      T i '' (sphere (0 : E2) 1 ×ˢ ({cut i} : Set ℝ)) := by
    ext y
    constructor
    · intro hy
      have hh := (hEshape i ▸ hy.1).1.2
      have hz : sign i * (H y - cut i) = 0 := le_antisymm hh (hNorthSide i y hy.2)
      have he : H y = cut i := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (hsignNe i))
      exact hEcut i ▸ ⟨hy.1, he⟩
    · intro hy
      have hemem : y ∈ E i ∩ {y | H y = cut i} := (hEcut i).symm ▸ hy
      exact ⟨hemem.1, hRimNorth i hy⟩
  have hCore (i : Fin 3) : (A i).closedRegion ∩ R ⊆ north i := by
    rintro y ⟨hyA, hyR⟩
    have hyB : y ∈ (A i).boundary := by
      rcases (A i).inside_union_boundary.symm ▸ hyA with hi | hb
      · exact False.elim (disjoint_left.mp (hAvoid i) hi hyR.1)
      · exact hb
    rcases (hA i).1 ▸ hyB with hyE | hyN
    · have hlo := (hEshape i ▸ hyE).1.2
      have hhi : 0 ≤ sign i * (H y - cut i) := by
        fin_cases i <;> norm_num [sign, cut] <;> linarith [hyR.2.1, hyR.2.2]
      have hz := (mul_eq_zero.mp (le_antisymm hlo hhi)).resolve_left (hsignNe i)
      exact hRimNorth i (hEcut i ▸ ⟨hyE, sub_eq_zero.mp hz⟩)
    · exact hyN
  have hNeg (i : Fin 3) (hi : i ≠ 2) (y : E3) (hy : y ∈ (A i).closedRegion) : H y < 0 := by
    fin_cases i
    · have hh := hA0h hy
      change H y ≤ cut 0 + lambda 0 * P.heightBound at hh
      change H y < 0
      have hs := hsmall 0
      dsimp [cut] at hh hs ⊢
      linarith
    · have hh := hA1h hy
      change H y ≤ cut 1 + lambda 1 * P.heightBound at hh
      change H y < 0
      have hs := hsmall 1
      dsimp [cut] at hh hs ⊢
      linarith
    · exact False.elim (hi rfl)
  have hPos (y : E3) (hy : y ∈ (A 2).closedRegion) : 1 < H y := by
    have hh := hA2h hy
    change cut 2 - lambda 2 * P.heightBound ≤ H y at hh
    change 1 < H y
    have hs := hsmall 2
    dsimp [cut] at hh hs ⊢
    linarith
  have hDisjoint (i k : Fin 3) (hik : i ≠ k) : Disjoint (A i).closedRegion (A k).closedRegion := by
    apply disjoint_left.mpr
    intro y hyi hyk
    by_cases hi : i = 2
    · subst i
      have hk : k ≠ 2 := Ne.symm hik
      linarith [hPos y hyi, hNeg k hk y hyk]
    by_cases hk : k = 2
    · subst k
      linarith [hNeg i hi y hyi, hPos y hyk]
    have hi_cases : i = (0 : Fin 3) ∨ i = (1 : Fin 3) := by
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact False.elim (hi rfl)
    have hk_cases : k = (0 : Fin 3) ∨ k = (1 : Fin 3) := by
      fin_cases k
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact False.elim (hk rfl)
    rcases hi_cases with rfl | rfl <;> rcases hk_cases with rfl | rfl
    · exact (hik rfl).elim
    · have hyi0 : y ∈ A0.closedRegion := by simpa [A] using hyi
      have hyk1 : y ∈ A1.closedRegion := by simpa [A] using hyk
      have hp0 := hA0s hyi0
      have hn1 := hA1s hyk1
      change 0 < ![1, -1] 0 * (J2 (L y).1).2 at hp0
      change 0 < ![1, -1] 1 * (J2 (L y).1).2 at hn1
      norm_num at hp0 hn1
      have hp : 0 < (J2 (L y).1).2 := hp0
      have hn : (J2 (L y).1).2 < 0 := hn1
      linarith
    · have hyi1 : y ∈ A1.closedRegion := by simpa [A] using hyi
      have hyk0 : y ∈ A0.closedRegion := by simpa [A] using hyk
      have hn1 := hA1s hyi1
      have hp0 := hA0s hyk0
      change 0 < ![1, -1] 1 * (J2 (L y).1).2 at hn1
      change 0 < ![1, -1] 0 * (J2 (L y).1).2 at hp0
      norm_num at hn1 hp0
      have hn : (J2 (L y).1).2 < 0 := hn1
      have hp : 0 < (J2 (L y).1).2 := hp0
      linarith
    · exact (hik rfl).elim
  have hNoZero (q : UnitTwoSphere) (hq : (q : E3) 1 = 0) : 0 ≤ H (j q) := by
    have hn : (q : E3) 0 ^ 2 + (q : E3) 1 ^ 2 + (q : E3) 2 ^ 2 = 1 := by
      have hh := congrArg (fun z : ℝ => z ^ 2) (norm_eq_of_mem_sphere q)
      simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, one_pow] using hh
    have hv : (q : E3) 0 ^ 2 ≤ 1 := by nlinarith [sq_nonneg ((q : E3) 2)]
    have hdq := (hdBounds ((q : E3) 0 ^ 2) (sq_nonneg _)).1
    rw [hjh, hq]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, add_zero]
    nlinarith [sq_nonneg ((q : E3) 2 + 1),
      mul_nonneg (sq_nonneg ((q : E3) 0)) (sub_nonneg.mpr hv)]
  have hCover : S = R ∪ (⋃ i : Fin 3, E i) := by
    apply Subset.antisymm
    · rintro y ⟨q, rfl⟩
      by_cases hlo : H (j q) < -1 / 8
      · have hn : (q : E3) 1 ≠ 0 := fun hq => by linarith [hNoZero q hq]
        rcases lt_or_gt_of_ne hn with hq | hq
        · exact Or.inr (mem_iUnion.mpr ⟨1, ⟨q, ⟨hq, hlo.le⟩, rfl⟩⟩)
        · exact Or.inr (mem_iUnion.mpr ⟨0, ⟨q, ⟨hq, hlo.le⟩, rfl⟩⟩)
      by_cases hhi : 3 / 2 ≤ H (j q)
      · exact Or.inr (mem_iUnion.mpr ⟨2, ⟨q, hhi, rfl⟩⟩)
      exact Or.inl ⟨⟨q, rfl⟩, le_of_not_gt hlo, (lt_of_not_ge hhi).le⟩
    · rintro y (hy | hy)
      · exact hy.1
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hy
        exact (hEshape i ▸ hi).1.1
  refine ⟨A, N, fun _ => 1 / 8, ?_, hDisjoint, hCover⟩
  intro i
  rcases hA i with ⟨hAb, hAc, hCuts, hPatch⟩
  rcases hN i with ⟨hNb, hNs, hNt, hNp, hNi, hNc, _⟩
  refine ⟨hAb, hAc, hAvoid i, hCore i, hRim i, hCuts, hNb, hNs, hNt,
    hNp, hNi, hNc, hNheight i, by norm_num, by norm_num, ?_⟩
  intro q hq
  rw [hNp]
  fin_cases i
  · have hq' : -1 / 8 < (heightCoordinates (q : E3)).2 := by norm_num at hq ⊢; exact hq
    simpa [cut, cap, sign] using hPatch q hq'
  · have hq' : -1 / 8 < (heightCoordinates (q : E3)).2 := by norm_num at hq ⊢; exact hq
    simpa [cut, cap, sign] using hPatch q hq'
  · have hq' : -1 / 8 < (heightCoordinates (q : E3)).2 := by norm_num at hq ⊢; exact hq
    simpa [cut, cap, sign] using hPatch q hq'

end PoincareConjecture.M25.Topology3D
