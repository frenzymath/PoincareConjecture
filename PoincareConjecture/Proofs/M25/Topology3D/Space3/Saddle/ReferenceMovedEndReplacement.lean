import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceMovedEndGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NorthCapEndTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CapHeightCompression
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold Topology InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

theorem exists_nonnested_reference_moved_end_replacement
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hdNear : ∀ q : ℝ, 0 ≤ q → q ≤ sigma / 2 →
      d q = Real.sqrt (1 - q) - 1 + q / 2)
    (hdZero : ∀ q : ℝ, sigma ≤ q → d q = 0)
    (hdBounds : ∀ q : ℝ, 0 ≤ q → -q ^ 2 / 2 ≤ d q ∧ d q ≤ 0)
    (hdDeriv : ∀ q : ℝ, 0 ≤ q → |deriv d q| ≤ 1 / 16)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (u : UnitTwoSphere) (P : SurgeryCapProfile)
    (m p tau : ℝ) (hm : m ∈ Ioo (-1 / 4 : ℝ) 0)
    (hp : p ∈ Ioo (0 : ℝ) 2) (htau : 0 < tau) :
    let L := heightPlaneCoordinates u
    let F : E3 → E3 := fun y =>
      L.symm (J2.symm (nonnestedReferenceDiffeomorph 0 d hd y).1,
        (nonnestedReferenceDiffeomorph 0 d hd y).2)
    let j : UnitTwoSphere → E3 := fun q => F (q : E3)
    let psi : UnitTwoSphere × ℝ → E3 := fun q => F ((1 + q.2) • (q.1 : E3))
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let S := range j
    let cut : Fin 3 → ℝ := ![m, m, p]
    let sign : Fin 3 → ℝ := ![1, 1, -1]
    let R := S ∩ {y | m ≤ H y ∧ H y ≤ p}
    let sector : Fin 3 → Set E3 := ![
      {y | 0 < (J2 (L y).1).2}, {y | (J2 (L y).1).2 < 0}, univ]
    let M := flatCapDiffeomorph P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
    IsCollarEmbedding psi ∧ S = F '' sphere (0 : E3) 1 ∧
    ∃ (b : ℝ) (T : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3),
      0 < b ∧ b < tau ∧ b < min (-m) p ∧ b < 1 / 256 ∧
      (∀ i : Fin 3,
        closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (T i).source ∧
        ContDiffOn ℝ ∞ (T i) (T i).source ∧
        ContDiffOn ℝ ∞ (T i).symm (T i).target ∧
        (∀ x ∈ (T i).source, H (T i x) = x.2) ∧
        (∀ y ∈ (T i).target, ((T i).symm y).2 = H y) ∧
        ∀ z : ℝ, |z - cut i| < b →
          T i '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
            S ∩ {y | H y = z} ∩ sector i) ∧
      ∀ lambda : Fin 3 → ℝ, (∀ i, 0 < lambda i) →
        (∀ i, lambda i * P.heightBound < b) →
        ∃ (N : Fin 3 → BallNeighborhoodChart E3 E3)
          (G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) (C : Set E3),
          let cap : Fin 3 → UnitTwoSphere → E3 := fun i =>
            P.capMap (T i) (cut i) (sign i) 0 (lambda i)
          let north : Fin 3 → Set E3 := fun i => cap i ''
            {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
          let south : Fin 3 → Set E3 := fun i => cap i ''
            {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
          (∀ i : Fin 3,
            (N i).boundary = south i ∪ north i ∧
            (N i).chart.source = {y : E3 |
              ((M (heightCoordinates y)).1,
                cut i + sign i * lambda i * (M (heightCoordinates y)).2) ∈ (T i).source} ∧
            (N i).chart.target = (T i).target ∧
            (∀ y : E3, (N i).chart y = T i ((M (heightCoordinates y)).1,
              cut i + sign i * lambda i * (M (heightCoordinates y)).2)) ∧
            (∀ y : E3, (N i).chart.symm y = heightCoordinates.symm
              (M.symm (((T i).symm y).1,
                (((T i).symm y).2 - cut i) / (sign i * lambda i)))) ∧
            (N i).closedRegion ⊆ F '' closedBall (0 : E3) 1 ∧
            (N i).closedRegion ⊆ {y | |H y - cut i| ≤ lambda i * P.heightBound} ∧
            (N i).closedRegion ⊆ {y | |H y - cut i| < tau}) ∧
          (∀ i k : Fin 3, i ≠ k → Disjoint (N i).closedRegion (N k).closedRegion) ∧
          G '' S = R ∪ (⋃ i : Fin 3, south i) ∧
          G.symm '' (R ∪ (⋃ i : Fin 3, south i)) = S ∧
          (∀ y ∈ R ∪ (⋃ i : Fin 3, north i), G y = y ∧ G.symm y = y) ∧
          IsCompact C ∧ C ⊆ (R ∪ (⋃ i : Fin 3, north i))ᶜ ∧
          tsupport (fun y : E3 => G y - y) ⊆ C ∧
          tsupport (fun y : E3 => G.symm y - y) ⊆ C ∧
          IsCollarEmbedding (fun q => G (psi q)) := by
  classical
  let L := heightPlaneCoordinates u
  let F : E3 → E3 := fun y =>
    L.symm (J2.symm (nonnestedReferenceDiffeomorph 0 d hd y).1,
      (nonnestedReferenceDiffeomorph 0 d hd y).2)
  let j : UnitTwoSphere → E3 := fun q => F (q : E3)
  let psi : UnitTwoSphere × ℝ → E3 := fun q => F ((1 + q.2) • (q.1 : E3))
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let S := range j
  let cut : Fin 3 → ℝ := ![m, m, p]
  let sign : Fin 3 → ℝ := ![1, 1, -1]
  let E : Fin 3 → Set E3 := ![
    j '' {q | 0 < (q : E3) 1 ∧ H (j q) ≤ m},
    j '' {q | (q : E3) 1 < 0 ∧ H (j q) ≤ m},
    j '' {q | p ≤ H (j q)}]
  let R := S ∩ {y | m ≤ H y ∧ H y ≤ p}
  let M := flatCapDiffeomorph P.horizontal P.vertical
    P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
  obtain ⟨hpsi, b, T, hb, hbTau, hbCuts, hbOld, hTube, hLater⟩ :=
    exists_nonnested_reference_moved_end_geometry sigma hsigma hsigmaSmall d hd
      hdNear hdZero hdBounds hdDeriv J2 hJ2 u P m p tau hm hp htau
  have hReference : S = F '' sphere (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨(q : E3), q.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let Fd := (nonnestedReferenceDiffeomorph 0 d hd).trans
    ((J2.symm.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).toDiffeomorph.trans
      L.symm.toDiffeomorph)
  have hScompact : IsCompact S := by
    change IsCompact (range (fun q : UnitTwoSphere => Fd (q : E3)))
    exact isCompact_range (Fd.continuous.comp continuous_subtype_val)
  have hRclosed : IsClosed R := hScompact.isClosed.inter
    ((isClosed_le continuous_const H.continuous).inter
      (isClosed_le H.continuous continuous_const))
  refine ⟨hpsi, hReference, b, T, hb, hbTau, hbCuts, hbOld, hTube, ?_⟩
  intro lambda hlambda hsmall
  obtain ⟨A, N, o, hGeometry, hDisjoint, hCover⟩ := hLater lambda hlambda hsmall
  choose hAb hAc _hAvoid hCore hRim hRim2 _hCuts hNb hNs hNt hNp hNi
    hNc hNh hNshort ho hoSmall hPatch using hGeometry
  let oldCap : Fin 3 → E3 → E3 := fun i y =>
    T i ((M (heightCoordinates y)).1,
      cut i + sign i * lambda i * (M (heightCoordinates y)).2)
  let oldNorth := fun i => oldCap i '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}
  let oldSouth := fun i => oldCap i '' {y : E3 | ‖y‖ = 1 ∧ (heightCoordinates y).2 ≤ 0}
  let cap : Fin 3 → UnitTwoSphere → E3 := fun i =>
    P.capMap (T i) (cut i) (sign i) 0 (lambda i)
  let north := fun i => cap i '' {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  let south := fun i => cap i '' {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  change S = R ∪ ⋃ i : Fin 3, E i at hCover
  change (∀ i, (A i).boundary = E i ∪ oldNorth i) at hAb
  change (∀ i, (N i).boundary = oldSouth i ∪ oldNorth i) at hNb
  change (∀ i, (A i).closedRegion ∩ R ⊆ oldNorth i) at hCore
  have hCap (i : Fin 3) (q : UnitTwoSphere) : oldCap i (q : E3) = cap i q := by
    change T i ((M (heightCoordinates (q : E3))).1,
      cut i + sign i * lambda i * (M (heightCoordinates (q : E3))).2) =
      T i ((M (heightCoordinates (q : E3))).1,
        cut i + sign i * (0 + lambda i * (M (heightCoordinates (q : E3))).2))
    apply congrArg (T i)
    apply Prod.ext
    · rfl
    · ring
  have hConvert (i : Fin 3) (f : ℝ → Prop) :
      oldCap i '' {y : E3 | ‖y‖ = 1 ∧ f (heightCoordinates y).2} =
        cap i '' {q : UnitTwoSphere | f (heightCoordinates (q : E3)).2} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxn, hxf⟩, hxy⟩
      let q : UnitTwoSphere := ⟨x, mem_sphere_zero_iff_norm.mpr hxn⟩
      exact ⟨q, hxf, (hCap i q).symm.trans hxy⟩
    · rintro ⟨q, hq, hqy⟩
      exact ⟨(q : E3), ⟨norm_eq_of_mem_sphere q, hq⟩, (hCap i q).trans hqy⟩
  have hNorth (i : Fin 3) : oldNorth i = north i := hConvert i (fun z => 0 ≤ z)
  have hSouth (i : Fin 3) : oldSouth i = south i := hConvert i (fun z => z ≤ 0)
  have hAn (i : Fin 3) : (A i).boundary = E i ∪ north i := by rw [hAb i, hNorth]
  have hNn (i : Fin 3) : (N i).boundary = south i ∪ north i := by rw [hNb i, hSouth, hNorth]
  have hNorthChart (i : Fin 3) : north i =
      (N i).chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
    rw [← hNorth i]
    exact image_congr (fun y _ => (hNp i y).symm)
  let K := fun i => R ∪ (⋃ k : Fin 3, ⋃ (_h : k ≠ i), (A k).closedRegion)
  have hKclosed (i : Fin 3) : IsClosed (K i) :=
    hRclosed.union (isClosed_iUnion_of_finite (fun k =>
      isClosed_iUnion_of_finite (fun _ => (A k).closedRegion_compact.isClosed)))
  have hGexists (i : Fin 3) :
      ∃ (G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) (C : Set E3),
        G '' E i = south i ∧ G.symm '' south i = E i ∧
        (∀ y ∈ north i ∪ K i, G y = y ∧ G.symm y = y) ∧
        IsCompact C ∧ C ⊆ (north i ∪ K i)ᶜ ∧
        tsupport (fun y => G y - y) ⊆ C ∧
        tsupport (fun y => G.symm y - y) ⊆ C := by
    have hA : (A i).boundary = E i ∪ (N i).chart ''
        {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
      rw [← hNorthChart]
      exact hAn i
    have hN : (N i).boundary = south i ∪ (N i).chart ''
        {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
      rw [← hNorthChart]
      exact hNn i
    have hmeet : E i ∩ (N i).chart ''
        {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} =
        south i ∩ (N i).chart ''
          {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
      rw [← hNorthChart, ← hNorth, ← hSouth]
      exact (hRim i).trans (hRim2 i).symm
    have hAK : (A i).closedRegion ∩ K i ⊆ (N i).chart ''
        {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
      rw [← hNorthChart, ← hNorth]
      rintro y ⟨hyA, hyR | hyO⟩
      · exact hCore i ⟨hyA, hyR⟩
      · obtain ⟨k, hk, hyk⟩ := mem_iUnion.mp hyO |>.imp (fun k => mem_iUnion.mp)
        exact False.elim (Set.disjoint_left.mp (hDisjoint i k hk.symm) hyA hyk)
    simpa only [← hNorthChart i] using
      exists_saddle_north_cap_end_transport (A i) (N i) (o i) (ho i)
        (by linarith [hoSmall i]) (hPatch i) (hNc i) (E i) (south i)
        (K i) (hKclosed i) hA hN hmeet hAK
  choose Gi Ci hGi _hGinv hGfix hCi hCsub hCsupp hCisupp using hGexists
  have hEclosed (i : Fin 3) : E i ⊆ (A i).closedRegion := by
    intro y hy
    rw [← (A i).inside_union_boundary, hAn]
    exact Or.inr (Or.inl hy)
  have hSouthclosed (i : Fin 3) : south i ⊆ (A i).closedRegion := by
    intro y hy
    apply hNc i
    rw [← (N i).inside_union_boundary, hNn]
    exact Or.inr (Or.inl hy)
  have hNorthclosed (i : Fin 3) : north i ⊆ (A i).closedRegion := by
    intro y hy
    apply hNc i
    rw [← (N i).inside_union_boundary, hNn]
    exact Or.inr (Or.inr hy)
  have hOther (i k : Fin 3) (hk : k ≠ i) :
      (A k).closedRegion ⊆ K i := by
    intro y hy
    exact Or.inr (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, hy⟩⟩)
  have hFixedImage (i : Fin 3) (X : Set E3) (hX : X ⊆ north i ∪ K i) :
      Gi i '' X = X := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [(hGfix i x (hX hx)).1] using hx
    · intro hy
      exact ⟨y, hy, (hGfix i y (hX hy)).1⟩
  have hGR (i : Fin 3) : Gi i '' R = R :=
    hFixedImage i R (fun _ hy => Or.inr (Or.inl hy))
  have hGE (i k : Fin 3) (hk : k ≠ i) : Gi i '' E k = E k :=
    hFixedImage i _ (fun _ hy => Or.inr (hOther i k hk (hEclosed k hy)))
  have hGS (i k : Fin 3) (hk : k ≠ i) : Gi i '' south k = south k :=
    hFixedImage i _ (fun _ hy => Or.inr (hOther i k hk (hSouthclosed k hy)))
  have hUnion3 (X : Fin 3 → Set E3) : (⋃ i, X i) = X 0 ∪ X 1 ∪ X 2 := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((hy | hy) | hy)
      · exact mem_iUnion.mpr ⟨0, hy⟩
      · exact mem_iUnion.mpr ⟨1, hy⟩
      · exact mem_iUnion.mpr ⟨2, hy⟩
  let G := ((Gi 0).trans (Gi 1)).trans (Gi 2)
  let C := ⋃ i : Fin 3, Ci i
  have hS0 : Gi 0 '' S = R ∪ (south 0 ∪ E 1 ∪ E 2) := by
    rw [hCover, hUnion3, image_union, image_union, image_union,
      hGR, hGi, hGE 0 1 (by decide), hGE 0 2 (by decide)]
  have hS01 : Gi 1 '' (Gi 0 '' S) = R ∪ (south 0 ∪ south 1 ∪ E 2) := by
    rw [hS0, image_union, image_union, image_union,
      hGR, hGS 1 0 (by decide), hGi, hGE 1 2 (by decide)]
  have hImage : G '' S = R ∪ (⋃ i : Fin 3, south i) := by
    calc
      _ = Gi 2 '' (Gi 1 '' (Gi 0 '' S)) := by rw [image_image, image_image]; rfl
      _ = R ∪ (south 0 ∪ south 1 ∪ south 2) := by
        rw [hS01, image_union, image_union, image_union,
          hGR, hGS 2 0 (by decide), hGS 2 1 (by decide), hGi]
      _ = _ := by rw [hUnion3]
  have hCompact : IsCompact C := isCompact_iUnion hCi
  have hCarrier : C ⊆ (R ∪ (⋃ i : Fin 3, north i))ᶜ := by
    intro y hy hprotect
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    apply hCsub i hi
    rcases hprotect with hyR | hyn
    · exact Or.inr (Or.inl hyR)
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hyn
      by_cases hki : k = i
      · subst k
        exact Or.inl hk
      · exact Or.inr (hOther i k hki (hNorthclosed k hk))
  have hFar (i : Fin 3) (y : E3) (hy : y ∉ Ci i) :
      Gi i y = y ∧ (Gi i).symm y = y := by
    constructor
    · by_contra hh
      exact hy (hCsupp i (subset_closure (sub_ne_zero.mpr hh)))
    · by_contra hh
      exact hy (hCisupp i (subset_closure (sub_ne_zero.mpr hh)))
  have hTotalFar (y : E3) (hy : y ∉ C) : G y = y ∧ G.symm y = y := by
    have hfar (i : Fin 3) := hFar i y (fun hi => hy (mem_iUnion.mpr ⟨i, hi⟩))
    change Gi 2 (Gi 1 (Gi 0 y)) = y ∧
      (Gi 0).symm ((Gi 1).symm ((Gi 2).symm y)) = y
    rw [(hfar 0).1, (hfar 1).1, (hfar 2).1,
      (hfar 2).2, (hfar 1).2, (hfar 0).2]
    exact ⟨rfl, rfl⟩
  refine ⟨N, G, C, ?_, ?_, hImage, ?_, ?_, hCompact, hCarrier, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hNn i, hNs i, hNt i, hNp i, hNi i, (hNc i).trans (hAc i), hNh i, hNshort i⟩
  · intro i k hik
    exact (hDisjoint i k hik).mono (hNc i) (hNc k)
  · rw [← hImage]
    exact G.symm_image_image S
  · intro y hy
    exact hTotalFar y (fun hC => hCarrier hC hy)
  · apply closure_minimal ?_ hCompact.isClosed
    intro y hy
    by_contra hyC
    exact hy (sub_eq_zero.mpr (hTotalFar y hyC).1)
  · apply closure_minimal ?_ hCompact.isClosed
    intro y hy
    by_contra hyC
    exact hy (sub_eq_zero.mpr (hTotalFar y hyC).2)
  · exact IsCollarEmbedding.postcompose_diffeomorph hpsi G

end PoincareConjecture.M25.Topology3D
