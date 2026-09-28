import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartDerivative
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothOpenChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalTubeChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartConjugation
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Support










set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

local notation "D2" => Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞
local notation "D3" => Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞




theorem planarDiffeomorphFamily_contDiff_symm
    (Phi : ℝ → D2)
    (hPhi : ContDiff ℝ ∞ (fun p : ℝ × E2 => Phi p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : ℝ × E2 => (Phi p.1).symm p.2) := by
  classical
  let F : ℝ × E2 → E2 := fun p => Phi p.1 p.2
  let B : ℝ × E2 → ℝ × E2 := fun p => (p.1, F p)
  let N : ℝ × E2 → ℝ × E2 := fun p => (p.1, (Phi p.1).symm p.2)
  have hF : ContDiff ℝ ∞ F := hPhi
  have hB : ContDiff ℝ ∞ B := contDiff_fst.prodMk hF
  have hNB (p : ℝ × E2) : N (B p) = p :=
    Prod.ext rfl ((Phi p.1).symm_apply_apply p.2)
  have hBN (p : ℝ × E2) : B (N p) = p :=
    Prod.ext rfl ((Phi p.1).apply_symm_apply p.2)
  have hBinj : Function.Injective B := by
    intro p q hpq
    exact (hNB p).symm.trans ((congrArg N hpq).trans (hNB q))
  have hd : ∀ p ∈ (univ : Set (ℝ × E2)),
      ∃ T : (ℝ × E2) ≃L[ℝ] (ℝ × E2),
        HasFDerivAt B (T : ℝ × E2 →L[ℝ] ℝ × E2) p := by
    intro p _hp
    let D : ℝ × E2 →L[ℝ] E2 := fderiv ℝ F p
    have hFD : HasFDerivAt F D p :=
      (hF.differentiable (by simp) p).hasFDerivAt
    let ep := (Phi p.1).toHomeomorph.toOpenPartialHomeomorph
    have hep : ContDiffOn ℝ ∞ ep ep.source :=
      (Phi p.1).contDiff.contDiffOn
    have hepi : ContDiffOn ℝ ∞ ep.symm ep.target :=
      (Phi p.1).symm.contDiff.contDiffOn
    have hxp : p.2 ∈ ep.source := mem_univ p.2
    obtain ⟨A, hA⟩ := exists_smoothChart_derivative ep hep hepi hxp
    have hA' : HasFDerivAt (fun x : E2 => F (p.1, x))
        (A : E2 →L[ℝ] E2) p.2 := hA
    have hsp : D.comp (ContinuousLinearMap.inr ℝ ℝ E2) =
        (A : E2 →L[ℝ] E2) := by
      have hFD' : HasFDerivAt F D (p.1, p.2) := hFD
      exact (hFD'.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)).unique hA'
    let T : (ℝ × E2) ≃L[ℝ] (ℝ × E2) :=
      (ContinuousLinearEquiv.refl ℝ ℝ).skewProd A
        (D.comp (ContinuousLinearMap.inl ℝ ℝ E2))
    have hT : (T : ℝ × E2 →L[ℝ] ℝ × E2) =
        (ContinuousLinearMap.fst ℝ ℝ E2).prod D := by
      apply ContinuousLinearMap.ext
      intro v
      apply Prod.ext
      · rfl
      · change A v.2 + D (v.1, 0) = D v
        have hAv : A v.2 = D (0, v.2) :=
          (congrArg (fun M : E2 →L[ℝ] E2 => M v.2) hsp).symm
        rw [hAv, ← map_add]
        simp
    refine ⟨T, ?_⟩
    rw [hT]
    exact hasFDerivAt_fst.prodMk hFD
  have hi : Set.InjOn B (univ : Set (ℝ × E2)) :=
    fun _ _ _ _ hpq => hBinj hpq
  let e := smoothOpenChart B isOpen_univ hB.contDiffOn hd hi
  have himage : B '' (univ : Set (ℝ × E2)) = univ := by
    ext p
    constructor
    · intro _hp
      exact mem_univ p
    · intro _hp
      exact ⟨N p, mem_univ _, hBN p⟩
  have heInvOn : ContDiffOn ℝ ∞ e.symm (univ : Set (ℝ × E2)) := by
    rw [← himage]
    exact smoothOpenChart_symm_contDiffOn B isOpen_univ hB.contDiffOn hd hi
  have heInv : (e.symm : ℝ × E2 → ℝ × E2) = N := by
    funext p
    have hp : p ∈ e.target := by
      change p ∈ B '' (univ : Set (ℝ × E2))
      rw [himage]
      exact mem_univ p
    apply hBinj
    calc
      B (e.symm p) = p := e.right_inv hp
      _ = B (N p) := (hBN p).symm
  have hN : ContDiff ℝ ∞ N := by
    rw [← heInv]
    exact contDiffOn_univ.mp heInvOn
  exact hN.snd





theorem exists_compact_planar_family_height_lift
    (Phi : ℝ → D2)
    (hPhi : ContDiff ℝ ∞ (fun p : ℝ × E2 => Phi p.1 p.2))
    (hzero : ∀ x : E2, Phi 0 x = x)
    (C : Set E2) (hC : IsCompact C)
    (hfix : ∀ t : ℝ, ∀ x : E2, x ∉ C → Phi t x = x)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hsChi : HasCompactSupport chi) (u : UnitTwoSphere) :
    let L := heightPlaneCoordinates u
    let K : Set E3 := L.symm '' (C ×ˢ tsupport chi)
    ∃ G : D3,
      (∀ x : E2, ∀ z : ℝ,
        G (L.symm (x, z)) = L.symm (Phi (chi z) x, z) ∧
        G.symm (L.symm (x, z)) = L.symm ((Phi (chi z)).symm x, z)) ∧
      IsCompact K ∧
      tsupport (fun y : E3 => G y - y) ⊆ K ∧
      tsupport (fun y : E3 => G.symm y - y) ⊆ K := by
  classical
  let L := heightPlaneCoordinates u
  let K : Set E3 := L.symm '' (C ×ˢ tsupport chi)
  have hInv := planarDiffeomorphFamily_contDiff_symm Phi hPhi
  let Psi : ℝ → D2 := fun z => Phi (chi z)
  have hPsi : ContDiff ℝ ∞ (fun p : ℝ × E2 => Psi p.1 p.2) :=
    hPhi.comp ((hchi.comp contDiff_fst).prodMk contDiff_snd)
  have hPsiInv : ContDiff ℝ ∞ (fun p : ℝ × E2 => (Psi p.1).symm p.2) :=
    hInv.comp ((hchi.comp contDiff_fst).prodMk contDiff_snd)
  let Q := planarFamilyGraphDiffeomorph Psi hPsi hPsiInv
  let G : D3 := (L.toDiffeomorph.trans Q).trans L.symm.toDiffeomorph
  have hformula (x : E2) (z : ℝ) :
      G (L.symm (x, z)) = L.symm (Phi (chi z) x, z) ∧
      G.symm (L.symm (x, z)) = L.symm ((Phi (chi z)).symm x, z) := by
    constructor
    · change L.symm (Q (L (L.symm (x, z)))) = _
      rw [L.apply_symm_apply]
      rfl
    · change L.symm (Q.symm (L (L.symm (x, z)))) = _
      rw [L.apply_symm_apply]
      rfl
  have hfixInv (t : ℝ) (x : E2) (hx : x ∉ C) : (Phi t).symm x = x :=
    equiv_symm_fixed_of_fixed (Phi t).toEquiv (hfix t x hx)
  have hzeroInv (x : E2) : (Phi 0).symm x = x :=
    equiv_symm_fixed_of_fixed (Phi 0).toEquiv (hzero x)
  have hK : IsCompact K :=
    (hC.prod hsChi.isCompact).image L.symm.continuous
  have hboth (y : E3) (hy : y ∉ K) : G y = y ∧ G.symm y = y := by
    let x : E2 := (L y).1
    let z : ℝ := (L y).2
    have hcoord : L.symm (x, z) = y := L.symm_apply_apply y
    obtain ⟨hf, hi⟩ := hformula x z
    by_cases hx : x ∈ C
    · have hz : z ∉ tsupport chi := by
        intro hz
        exact hy ⟨(x, z), ⟨hx, hz⟩, hcoord⟩
      have hc : chi z = 0 := image_eq_zero_of_notMem_tsupport hz
      have hf0 : Phi (chi z) x = x := by
        rw [hc]
        exact hzero x
      have hi0 : (Phi (chi z)).symm x = x := by
        rw [hc]
        exact hzeroInv x
      rw [hf0, hcoord] at hf
      rw [hi0, hcoord] at hi
      exact ⟨hf, hi⟩
    · rw [hfix (chi z) x hx, hcoord] at hf
      rw [hfixInv (chi z) x hx, hcoord] at hi
      exact ⟨hf, hi⟩
  refine ⟨G, hformula, hK, ?_, ?_⟩
  · apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hyK
    exact hy (sub_eq_zero.mpr (hboth y hyK).1)
  · apply closure_minimal ?_ hK.isClosed
    intro y hy
    by_contra hyK
    exact hy (sub_eq_zero.mpr (hboth y hyK).2)

end PoincareConjecture.M25.Topology3D
