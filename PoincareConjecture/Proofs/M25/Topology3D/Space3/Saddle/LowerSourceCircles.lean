import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerLevelTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceSurfacePullback
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_lower_source_circles
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D) (a : ℝ)
    (hla : W.level ≤ a)
    (hac : a < ⟪(u : E3), psi (D.point, 0)⟫_ℝ) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let L := heightPlaneCoordinates u
    let pi := horizontalBandProjection u
    let c0 : Fin 2 → UnitCircle → E2 := fun i theta =>
      pi (j (W.leg i (theta, W.level)))
    let m := (W.level + a) / 2
    (∀ q : UnitTwoSphere,
      ⟪(u : E3), j q⟫_ℝ ∈ Icc W.level a → q ∈ D.sourceCore ∧
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
          (fun p : UnitTwoSphere => ⟪(u : E3), j p⟫_ℝ) q ≠ 0) ∧
    (∀ i : Fin 2, IsPlanarEmbedding (c0 i) ∧ range (c0 i) = (W.disc i).boundary) ∧
    ∃ (d : ℝ)
      (T : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
      (q : Fin 2 → UnitCircle → UnitTwoSphere),
    let C : Fin 2 → ℝ → UnitCircle → E2 := fun i z theta => T z (c0 i theta)
    let B : ℝ → Fin 2 → BallNeighborhoodChart E2 E2 :=
      fun z i => (W.disc i).mapDiffeomorph (T z)
    0 < d ∧ Icc W.level a ⊆ Ioo (m - d) (m + d) ∧
    ContDiff ℝ ∞ (fun p : ℝ × E2 => T p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : ℝ × E2 => (T p.1).symm p.2) ∧
    (∀ x : E2, T W.level x = x) ∧
    (∀ z : ℝ, HasCompactSupport (fun x => T z x - x) ∧
      HasCompactSupport (fun x => (T z).symm x - x)) ∧
    (∀ i : Fin 2,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : ℝ × UnitCircle => C i p.1 p.2) ∧
      ∀ z : ℝ, IsPlanarEmbedding (C i z) ∧ range (C i z) = (B z i).boundary) ∧
    (∀ z : ℝ, Disjoint (B z 0).boundary (B z 1).boundary) ∧
    (∀ z ∈ Ioo (m - d) (m + d), ∀ x : E2,
      (L.symm (T z x, z) ∈ range j ↔ L.symm (x, W.level) ∈ range j)) ∧
    (∀ z ∈ Ioo (m - d) (m + d),
      {x : E2 | L.symm (x, z) ∈ range j} = ⋃ i : Fin 2, (B z i).boundary) ∧
    (∀ z : ℝ,
      (Disjoint (B z 0).closedRegion (B z 1).closedRegion ↔
        Disjoint (W.disc 0).closedRegion (W.disc 1).closedRegion) ∧
      ((B z 0).closedRegion ⊆ (B z 1).inside ↔
        (W.disc 0).closedRegion ⊆ (W.disc 1).inside) ∧
      ((B z 1).closedRegion ⊆ (B z 0).inside ↔
        (W.disc 1).closedRegion ⊆ (W.disc 0).inside)) ∧
    (∀ i : Fin 2,
      ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Function.Injective (q i) ∧
      ∀ theta : UnitCircle,
        Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q i) theta)) ∧
    (∀ i k : Fin 2, i ≠ k → Disjoint (range (q i)) (range (q k))) ∧
    (⋃ i : Fin 2, range (q i)) =
      {p : UnitTwoSphere | ⟪(u : E3), j p⟫_ℝ = a} ∧
    ∀ (i : Fin 2) (theta : UnitCircle),
      j (q i theta) =
        L.symm (T a (pi (j (W.leg i (theta, W.level)))), a) := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let L := heightPlaneCoordinates u
  let pi := horizontalBandProjection u
  have hji : Injective j := by
    intro p q hpq
    exact congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpq)
  obtain ⟨hreg, hc0, d, T, hd, hI, hTs, hTi, hT0, hSupp,
    hC, hDis, hMembership, hCover, hCases⟩ :=
    exists_saddle_lower_level_transport psi hpsi u D W a hla hac
  let C : Fin 2 → UnitCircle → E2 := fun i theta =>
    T a (pi (j (W.leg i (theta, W.level))))
  let ca : Fin 2 → UnitCircle → E3 := fun i theta => L.symm (C i theta, a)
  have hemb (i : Fin 2) : IsPlanarEmbedding (C i) := ((hC i).2 a).1
  have hCa : {x : E2 | L.symm (x, a) ∈ range j} =
      ⋃ i : Fin 2, range (C i) := by
    rw [hCover a (hI ⟨hla, le_rfl⟩)]
    exact iUnion_congr (fun i => ((hC i).2 a).2.symm)
  have hCadis : Disjoint (range (C 0)) (range (C 1)) := by
    rw [((hC 0).2 a).2, ((hC 1).2 a).2]
    exact hDis a
  have hcaproj (i : Fin 2) : pi ∘ ca i = C i := by
    funext theta
    change (L (L.symm (C i theta, a))).1 = C i theta
    rw [L.apply_symm_apply]
  have hcaproj_apply (i : Fin 2) (theta : UnitCircle) : pi (ca i theta) = C i theta :=
    congrFun (hcaproj i) theta
  have hlift (i : Fin 2) : ∃ q : UnitCircle → UnitTwoSphere,
      ContMDiff (𝓡 1) (𝓡 2) ∞ q ∧ Injective q ∧
      (∀ theta, Injective (mfderiv (𝓡 1) (𝓡 2) q theta)) ∧
      ∀ theta, j (q theta) = ca i theta := by
    have hcs : ContMDiff (𝓡 1) 𝓘(ℝ, E3) ∞ (ca i) :=
      L.symm.contDiff.contMDiff.comp ((hemb i).1.prodMk_space contMDiff_const)
    have hci : Injective (ca i) := by
      intro s t hst
      apply (hemb i).2.1
      simpa only [hcaproj_apply] using congrArg pi hst
    have hcd (theta : UnitCircle) : Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3) (ca i) theta) := by
      have hpim : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, E2) ∞ pi := pi.contDiff.contMDiff
      have hh := (hpim.mdifferentiable (by simp) (ca i theta)).hasMFDerivAt.comp
        theta (hcs.mdifferentiable (by simp) theta).hasMFDerivAt
      rw [hcaproj] at hh
      intro x y hxy
      apply (hemb i).2.2 theta
      rw [hh.mfderiv]
      exact congrArg (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E2) pi (ca i theta)) hxy
    have hcentral : MapsTo (ca i) univ (range j) := by
      intro theta _
      have ht : C i theta ∈ ⋃ k : Fin 2, range (C k) :=
        mem_iUnion.mpr ⟨i, ⟨theta, rfl⟩⟩
      rw [← hCa] at ht
      exact ht
    obtain ⟨q, hqs, hqi, hqd, hqr⟩ := exists_collar_surface_source_pullback
      (𝓡 1) psi hpsi (ca i) isOpen_univ hcs.contMDiffOn hci.injOn
      (fun theta _ => hcd theta) hcentral
    exact ⟨q, contMDiffOn_univ.mp hqs, fun x y h => hqi (mem_univ _) (mem_univ _) h,
      fun theta => hqd theta (mem_univ _), fun theta => hqr theta (mem_univ _)⟩
  choose q hqs hqi hqd hqr using hlift
  have hq (i : Fin 2) : ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Injective (q i) ∧
      ∀ theta, Injective (mfderiv (𝓡 1) (𝓡 2) (q i) theta) :=
    ⟨hqs i, hqi i, hqd i⟩
  have hqdis : Disjoint (range (q 0)) (range (q 1)) := by
    apply disjoint_left.mpr
    rintro x ⟨s, rfl⟩ ⟨t, ht⟩
    have hh : C 1 t = C 0 s := by
      have hjj := congrArg j ht
      rw [hqr 1 t, hqr 0 s] at hjj
      simpa only [hcaproj_apply] using congrArg pi hjj
    exact disjoint_left.mp hCadis ⟨s, rfl⟩ ⟨t, hh⟩
  have hqpair (i k : Fin 2) (hik : i ≠ k) : Disjoint (range (q i)) (range (q k)) := by
    fin_cases i <;> fin_cases k <;>
      first | exact False.elim (hik rfl) | exact hqdis | exact hqdis.symm
  have hqlevel : (⋃ i : Fin 2, range (q i)) =
      {p : UnitTwoSphere | ⟪(u : E3), j p⟫_ℝ = a} := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, theta, rfl⟩ := mem_iUnion.mp hx
      change ⟪(u : E3), j (q i theta)⟫_ℝ = a
      rw [hqr, ← heightPlaneCoordinates_snd u]
      change (L (L.symm (C i theta, a))).2 = a
      rw [L.apply_symm_apply]
    · intro hx
      have hrec : L.symm (pi (j x), a) = j x :=
        heightPlaneCoordinates_reconstruct u (j x) a hx
      have hm : pi (j x) ∈ ⋃ i : Fin 2, range (C i) := by
        rw [← hCa]
        change L.symm (pi (j x), a) ∈ range j
        rw [hrec]
        exact ⟨x, rfl⟩
      obtain ⟨i, theta, ht⟩ := mem_iUnion.mp hm
      refine mem_iUnion.mpr ⟨i, ⟨theta, hji ?_⟩⟩
      rw [hqr]
      change L.symm (C i theta, a) = j x
      rw [ht, hrec]
  exact ⟨hreg, hc0, d, T, q, hd, hI, hTs, hTi, hT0, hSupp,
    hC, hDis, hMembership, hCover, hCases, hq, hqpair, hqlevel, hqr⟩

end PoincareConjecture.M25.Topology3D
