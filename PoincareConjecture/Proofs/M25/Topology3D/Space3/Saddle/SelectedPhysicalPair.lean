import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NonnestedPairArcIsotopy
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallTransport
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Calculus.Deriv.Comp










set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

set_option linter.unusedVariables false in




theorem exists_saddle_selected_physical_pair
    (hP : PlanarSchoenfliesService)
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (hkappa : ContDiffOn ℝ ∞ kappa kappa.source)
    (hkappaInv : ContDiffOn ℝ ∞ kappa.symm kappa.target)
    (gRef : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (hgRef : EqOn gRef kappa (closedBall (0 : E2) 2))
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (mu : ℝ) (hmu : 0 < mu) (hmuSmall : mu ≤ 1 / 128)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hchiBounds : ∀ r : ℝ, 0 ≤ chi r ∧ chi r ≤ 1)
    (hchiSupport : tsupport chi ⊆ Ioo (1 / 2 : ℝ) (3 / 2))
    (hchiOne : ∀ r ∈ Icc (3 / 4 : ℝ) (5 / 4), chi r = 1) :
    let F : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
      Classical.choose (exists_saddle_angular_reconnection
        J2 hJ2 mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let port : Fin 4 → E2 := fun k =>
      J2.symm (sx k / Real.sqrt 2, sy k / Real.sqrt 2)
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let K := kappa '' closedBall (0 : E2) 1
    let sign : Fin 2 → ℝ := ![1, -1]
    let Z : Fin 2 → Set E2 := fun i =>
      {x | ‖x‖ ≤ 1 ∧ (J2 x).2 = sign i * Real.sqrt ((J2 x).1 ^ 2 + mu)}
    let Eta : Fin 2 → Set E2 := fun i => (F 1) '' Z i
    ∀ (nuT : ℝ) (hnuT : 0 < nuT) (alphaT : Fin 2 → ℝ → E2)
      (hTargetArcs : ∀ i : Fin 2,
        ContDiff ℝ ∞ (alphaT i) ∧
        (∀ t : ℝ, deriv (alphaT i) t ≠ 0) ∧
        InjOn (alphaT i) (Icc (-nuT) (1 + nuT)))
      (hTargetPair : ∀ i k : Fin 2, i ≠ k →
        Disjoint (alphaT i '' Icc (-nuT) (1 + nuT))
          (alphaT k '' Icc (-nuT) (1 + nuT)))
      (hTargetProper : ∀ i t, t ∈ Ioo (0 : ℝ) 1 → alphaT i t ∉ K)
      (hTargetStart : ∀ i t, t ∈ Icc (-nuT) nuT →
        alphaT i t = kappa ((1 + t) • port (ep (i, 0))))
      (hTargetFinish : ∀ i t, t ∈ Icc (1 - nuT) (1 + nuT) →
        alphaT i t = kappa ((2 - t) • port (ep (i, 1))))
      (BT : Fin 2 → BallNeighborhoodChart E2 E2)
      (hTargetBoundary : ∀ i, (BT i).boundary =
        (alphaT i '' Icc (0 : ℝ) 1) ∪ (kappa '' Eta i))
      (hTargetCase : Disjoint (BT 0).closedRegion (BT 1).closedRegion)
      (nuR : ℝ) (hnuR : 0 < nuR) (hnuRSmall : nuR < 1 / 16)
      (alphaRef : Fin 2 → ℝ → E2)
      (hReferenceArcs : ∀ i : Fin 2,
        ContDiffOn ℝ ∞ (alphaRef i) (Ioo (-nuR) (1 + nuR)) ∧
        InjOn (alphaRef i) (Ioo (-nuR) (1 + nuR)) ∧
        (∀ t ∈ Ioo (-nuR) (1 + nuR), deriv (alphaRef i) t ≠ 0) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, 0 < sign i * (J2 (alphaRef i t)).2) ∧
        (∀ t ∈ Ioo (0 : ℝ) 1, 1 < ‖alphaRef i t‖) ∧
        (∀ t : ℝ, |t| < nuR →
          alphaRef i t = (1 + t) • port (ep (i, 0))) ∧
        (∀ t : ℝ, |t - 1| < nuR →
          alphaRef i t = (2 - t) • port (ep (i, 1))))
      (hReferencePair : Disjoint (alphaRef 0 '' Icc (0 : ℝ) 1)
        (alphaRef 1 '' Icc (0 : ℝ) 1))
      (cRef : Fin 2 → UnitCircle → E2)
      (BRef : Fin 2 → BallNeighborhoodChart E2 E2)
      (hReferenceImage : ∀ i, range (cRef i) =
        (alphaRef i '' Icc (0 : ℝ) 1) ∪ Eta i)
      (hReferenceBoundary : ∀ i, (BRef i).boundary = range (cRef i))
      (hReferenceCase : Disjoint (BRef 0).closedRegion (BRef 1).closedRegion),
      let nu := min nuT nuR / 2
      let alpha : Fin 2 → Fin 2 → ℝ → E2 :=
        ![fun i t => gRef (alphaRef i t), alphaT]
      ∃ (l r eta : ℝ) (C : Set E2)
        (J : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞),
      let Tailpar : Set ℝ := Icc 0 l ∪ Icc r 1
      0 < l ∧ l < r ∧ r < 1 ∧ l < nu ∧ 1 - nu < r ∧
      0 < eta ∧ eta < l ∧ r + eta < 1 ∧ l + eta < r - eta ∧
      IsCompact C ∧
      ContDiff ℝ ∞ (fun p : ℝ × E2 => J p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E2 => (J p.1).symm p.2) ∧
      (∀ s : ℝ, s ≤ 0 → ∀ y : E2, J s y = y ∧ (J s).symm y = y) ∧
      (∀ s : ℝ, 1 ≤ s → ∀ y : E2,
        J s y = J 1 y ∧ (J s).symm y = (J 1).symm y) ∧
      (∀ s : ℝ,
        tsupport (fun y : E2 => J s y - y) ⊆ C ∧
        tsupport (fun y : E2 => (J s).symm y - y) ⊆ C) ∧
      (∀ s : ℝ, ∀ y : E2, y ∉ C → J s y = y ∧ (J s).symm y = y) ∧
      IsOpen Cᶜ ∧ K ⊆ Cᶜ ∧
      (∀ j i : Fin 2, alpha j i '' Tailpar ⊆ Cᶜ) ∧
      (∀ i : Fin 2, ∀ t ∈ Icc (0 : ℝ) 1,
        J 1 (gRef (alphaRef i t)) = alphaT i t ∧
        (J 1).symm (alphaT i t) = gRef (alphaRef i t)) ∧
      ∀ i : Fin 2,
        (J 1) '' ((fun t => gRef (alphaRef i t)) '' Icc (0 : ℝ) 1) =
          alphaT i '' Icc (0 : ℝ) 1 ∧
        (J 1).symm '' (alphaT i '' Icc (0 : ℝ) 1) =
          (fun t => gRef (alphaRef i t)) '' Icc (0 : ℝ) 1 := by
  classical
  dsimp only
  intro nuT hnuT alphaT hTargetArcs hTargetPair hTargetProper hTargetStart
    hTargetFinish BT hTargetBoundary hTargetCase nuR hnuR hnuRSmall
    alphaRef hReferenceArcs hReferencePair cRef BRef hReferenceImage
    hReferenceBoundary hReferenceCase
  let F := Classical.choose (exists_saddle_angular_reconnection
    J2 hJ2 mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne)
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let port : Fin 4 → E2 := fun k =>
    J2.symm (sx k / Real.sqrt 2, sy k / Real.sqrt 2)
  let sign : Fin 2 → ℝ := ![1, -1]
  let Z : Fin 2 → Set E2 := fun i =>
    {x | ‖x‖ ≤ 1 ∧ (J2 x).2 = sign i * Real.sqrt ((J2 x).1 ^ 2 + mu)}
  let Eta : Fin 2 → Set E2 := fun i => (F 1) '' Z i
  let K : Set E2 := kappa '' closedBall (0 : E2) 1
  let nu : ℝ := min nuT nuR / 2
  let alpha : Fin 2 → Fin 2 → ℝ → E2 :=
    ![fun i t => gRef (alphaRef i t), alphaT]
  let B : Fin 2 → Fin 2 → BallNeighborhoodChart E2 E2 :=
    ![fun i => (BRef i).mapDiffeomorph gRef, BT]
  have hmin : 0 < min nuT nuR := lt_min hnuT hnuR
  have hnu : 0 < nu := half_pos hmin
  have hnuT' : nu < nuT := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hnuR' : nu < nuR := (half_lt_self hmin).trans_le (min_le_right _ _)
  have hnuSmall : nu < 1 / 16 := hnuR'.trans hnuRSmall
  have hToTarget : Ioo (-nu) (1 + nu) ⊆ Icc (-nuT) (1 + nuT) := by
    intro t ht
    exact ⟨by linarith only [ht.1, hnuT'], by linarith only [ht.2, hnuT']⟩
  have hToReference : Ioo (-nu) (1 + nu) ⊆ Ioo (-nuR) (1 + nuR) := by
    intro t ht
    exact ⟨by linarith only [ht.1, hnuR'], by linarith only [ht.2, hnuR']⟩
  have hUnitTarget : Icc (0 : ℝ) 1 ⊆ Icc (-nuT) (1 + nuT) := by
    intro t ht
    exact ⟨by linarith only [ht.1, hnuT], by linarith only [ht.2, hnuT]⟩
  have hPortNorm (k : Fin 4) : ‖port k‖ = 1 := by
    have hs : (sx k) ^ 2 = 1 ∧ (sy k) ^ 2 = 1 := by
      fin_cases k <;> norm_num [sx, sy]
    have hn := hJ2 (port k)
    simp only [port, ContinuousLinearEquiv.apply_symm_apply, div_pow,
      hs.1, hs.2, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hn
    nlinarith only [hn, norm_nonneg (port k)]
  have hOneTwo : closedBall (0 : E2) 1 ⊆ closedBall (0 : E2) 2 :=
    closedBall_subset_closedBall (by norm_num)
  have hNorm := (Classical.choose_spec (exists_saddle_angular_reconnection
    J2 hJ2 mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne)).2.2.2.1
  have hEta (i : Fin 2) : Eta i ⊆ closedBall (0 : E2) 1 := by
    rintro y ⟨x, hx, rfl⟩
    rw [mem_closedBall_zero_iff, (hNorm 1 x).1]
    exact hx.1
  have hEtaImage (i : Fin 2) : gRef '' Eta i = kappa '' Eta i :=
    image_congr (fun x hx => hgRef (hOneTwo (hEta i hx)))
  have hSmooth (j i : Fin 2) :
      ContDiffOn ℝ ∞ (alpha j i) (Ioo (-nu) (1 + nu)) := by
    fin_cases j
    · exact gRef.contDiff.comp_contDiffOn ((hReferenceArcs i).1.mono hToReference)
    · exact (hTargetArcs i).1.contDiffOn
  have hInj (j i : Fin 2) : InjOn (alpha j i) (Ioo (-nu) (1 + nu)) := by
    fin_cases j
    · intro t ht s hs heq
      exact (hReferenceArcs i).2.1 (hToReference ht) (hToReference hs)
        (gRef.injective heq)
    · exact (hTargetArcs i).2.2.mono hToTarget
  have hRegular (j i : Fin 2) (t : ℝ) (ht : t ∈ Ioo (-nu) (1 + nu)) :
      deriv (alpha j i) t ≠ 0 := by
    fin_cases j
    · have htR := hToReference ht
      have hf : DifferentiableAt ℝ (alphaRef i) t :=
        ((hReferenceArcs i).1.contDiffAt (isOpen_Ioo.mem_nhds htR)).differentiableAt
          (by simp)
      have hg := (gRef.contDiff.differentiable (by simp) (alphaRef i t)).hasFDerivAt
      have hd := hg.comp_hasDerivAt t hf.hasDerivAt
      have hi : Injective (fderiv ℝ gRef (alphaRef i t)) := by
        rw [← mfderiv_eq_fderiv]
        exact (gRef.toOpenPartialHomeomorph_mdifferentiable
          (by simp)).mfderiv_injective (mem_univ _)
      intro hz
      change deriv (gRef ∘ alphaRef i) t = 0 at hz
      rw [hd.deriv] at hz
      exact (hReferenceArcs i).2.2.1 t htR (hi (by simpa only [map_zero] using hz))
    · exact (hTargetArcs i).2.1 t
  have hPair (j : Fin 2) : Disjoint (alpha j 0 '' Icc (0 : ℝ) 1)
      (alpha j 1 '' Icc (0 : ℝ) 1) := by
    fin_cases j
    · change Disjoint ((gRef ∘ alphaRef 0) '' Icc (0 : ℝ) 1)
        ((gRef ∘ alphaRef 1) '' Icc (0 : ℝ) 1)
      rw [image_comp, image_comp]
      exact disjoint_image_of_injective gRef.injective hReferencePair
    · exact (hTargetPair 0 1 (by decide)).mono (image_mono hUnitTarget)
        (image_mono hUnitTarget)
  have hProper (j i : Fin 2) : alpha j i '' Ioo (0 : ℝ) 1 ⊆ Kᶜ := by
    fin_cases j
    · rintro y ⟨t, ht, rfl⟩ ⟨x, hx, heq⟩
      have hh : x = alphaRef i t := gRef.injective ((hgRef (hOneTwo hx)).trans heq)
      have hn := mem_closedBall_zero_iff.mp hx
      rw [hh] at hn
      exact (not_lt_of_ge hn) ((hReferenceArcs i).2.2.2.2.1 t ht)
    · rintro y ⟨t, ht, rfl⟩
      exact hTargetProper i t ht
  have hStart (j i : Fin 2) (t : ℝ) (ht : |t| < nu) :
      alpha j i t = kappa ((1 + t) • port (finProdFinEquiv (i, (0 : Fin 2)))) := by
    have hbounds := abs_lt.mp ht
    fin_cases j
    · change gRef (alphaRef i t) = _
      rw [(hReferenceArcs i).2.2.2.2.2.1 t (ht.trans hnuR')]
      apply hgRef
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        hPortNorm, mul_one, abs_of_pos (by linarith only [hbounds.1, hnuSmall])]
      linarith only [hbounds.2, hnuSmall]
    · exact hTargetStart i t
        ⟨by linarith only [hbounds.1, hnuT'], by linarith only [hbounds.2, hnuT']⟩
  have hFinish (j i : Fin 2) (t : ℝ) (ht : |t - 1| < nu) :
      alpha j i t = kappa ((2 - t) • port (finProdFinEquiv (i, (1 : Fin 2)))) := by
    have hbounds := abs_lt.mp ht
    fin_cases j
    · change gRef (alphaRef i t) = _
      rw [(hReferenceArcs i).2.2.2.2.2.2 t (ht.trans hnuR')]
      apply hgRef
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
        hPortNorm, mul_one, abs_of_pos (by linarith only [hbounds.2, hnuSmall])]
      linarith only [hbounds.1, hnuSmall]
    · exact hTargetFinish i t
        ⟨by linarith only [hbounds.1, hnuT'], by linarith only [hbounds.2, hnuT']⟩
  have hBoundary (j i : Fin 2) : (B j i).boundary =
      (alpha j i '' Icc (0 : ℝ) 1) ∪ (kappa '' Eta i) := by
    fin_cases j
    · change ((BRef i).mapDiffeomorph gRef).boundary =
        (gRef ∘ alphaRef i) '' Icc (0 : ℝ) 1 ∪ kappa '' Eta i
      rw [BallNeighborhoodChart.mapDiffeomorph_boundary, hReferenceBoundary,
        hReferenceImage, image_union, hEtaImage, image_comp]
    · exact hTargetBoundary i
  have hCase (j : Fin 2) : Disjoint (B j 0).closedRegion (B j 1).closedRegion := by
    fin_cases j
    · change Disjoint ((BRef 0).mapDiffeomorph gRef).closedRegion
        ((BRef 1).mapDiffeomorph gRef).closedRegion
      rw [BallNeighborhoodChart.mapDiffeomorph_closedRegion,
        BallNeighborhoodChart.mapDiffeomorph_closedRegion]
      exact disjoint_image_of_injective gRef.injective hReferenceCase
    · exact hTargetCase
  exact exists_nonnested_pair_arc_isotopy hP kappa hkappaSource hkappa hkappaInv
    J2 hJ2 (fun _ => mu) (fun _ => hmu) (fun _ => hmuSmall)
    chi hchi hchiBounds hchiSupport hchiOne nu hnu hnuSmall alpha
    hSmooth hInj hRegular hPair hProper hStart hFinish B hBoundary hCase

end PoincareConjecture.M25.Topology3D
