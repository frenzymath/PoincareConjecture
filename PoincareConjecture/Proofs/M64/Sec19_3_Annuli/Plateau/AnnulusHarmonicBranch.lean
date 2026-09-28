import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.DouglasMorreyInterface
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.HarmonicBranchConnected
import PoincareConjecture.Proofs.M60.Mathlib.ManifoldDerivativeEquiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem m64Annulus_finite_branch_set_of_global_harmonic_chart
    (A : M64Annulus g c0 c1) (b : M) (u : ℂ → E)
    (hsource : ∀ p : LoopPlane,
      u (Complex.orthonormalBasisOneI.repr.symm p) ∈
        (extChartAt (𝓡 n) b).target)
    (hfactor : ∀ p : LoopPlane,
      A.map p = (extChartAt (𝓡 n) b).symm
        (u (Complex.orthonormalBasisOneI.repr.symm p)))
    (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (hu : ContDiffOn ℝ 2 u (Set.univ : Set ℂ))
    (hΓ : ∀ z : ℂ, ContDiffAt ℝ 1 Γ (u z))
    (hsym : ∀ z : ℂ, ∀ a b : E,
      Γ (u z) a b = Γ (u z) b a)
    (hτ : ∀ z : ℂ,
      ConnectionVariation.covDerivAlong
          Γ u
          (fun w => fderiv ℝ u w 1) 1 z +
        ConnectionVariation.covDerivAlong
          Γ u
          (fun w => fderiv ℝ u w Complex.I) Complex.I z = 0)
    (hnonconstant : ∃ x : ℂ, ∃ y : ℂ, u x ≠ u y) :
    (m64AnnulusBranchSet A).Finite := by
  let c := extChartAt (𝓡 n) b
  let C := Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let D := Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv
  have hCD (p : LoopPlane) : C (D p) = p := by
    change (Complex.orthonormalBasisOneI.repr : ℂ → LoopPlane)
        (Complex.orthonormalBasisOneI.repr.symm p) = p
    exact Complex.orthonormalBasisOneI.repr.apply_symm_apply p
  have hcoord (p : LoopPlane) :
      c (A.map p) = u (D p) := by
    have hsp : u (D p) ∈ c.target := by
      change u (Complex.orthonormalBasisOneI.repr.symm p) ∈ c.target
      simpa only [c] using hsource p
    have hp : c.symm (u (D p)) ∈ c.source := c.map_target hsp
    rw [hfactor p]
    exact c.right_inv hsp
  have hbranch_to_zero (p : LoopPlane)
      (hp : p ∈ m64AnnulusBranchSet A) :
      fderiv ℝ u (D p) = 0 := by
    have hpint : p ∈ interior m64AnnulusDomain := hp.1
    have hpmem : p ∈ m64AnnulusDomain := interior_subset hpint
    have htarget : u (D p) ∈ c.target := by
      change u (Complex.orthonormalBasisOneI.repr.symm p) ∈ c.target
      simpa only [c] using hsource p
    have hchartsource : A.map p ∈ c.source := by
      rw [hfactor p]
      exact c.map_target htarget
    have hc : MDifferentiableAt (𝓡 n) (𝓘(ℝ, E)) c (A.map p) := by
      exact mdifferentiableAt_extChartAt (by simpa only [c, extChartAt_source]
        using hchartsource)
    have hAcomp : MDifferentiableAt (𝓡 2) (𝓡 n) A.map p := by
      have hsymm : ContMDiffAt (𝓘(ℝ, E)) (𝓡 n) ∞ c.symm (u (D p)) := by
        exact (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) b _ htarget).contMDiffAt
          ((isOpen_extChartAt_target b).mem_nhds htarget)
      have hD : MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℂ)) D p :=
        D.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
      have huAt : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓘(ℝ, E)) u (D p) := by
        exact (hu.contDiffAt (isOpen_univ.mem_nhds (mem_univ _))).contMDiffAt.mdifferentiableAt
          (by simp)
      have hcomp := (hsymm.mdifferentiableAt (by simp)).comp p
        (huAt.comp p hD)
      apply hcomp.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall (fun q => by
        change A.map q = c.symm (u (D q))
        exact hfactor q)
    have hchain := mfderiv_comp p hc hAcomp
    rw [mfderiv_eq_fderiv] at hchain
    have hcoordzero : fderiv ℝ (c ∘ A.map) p = 0 := by
      rw [hchain, hp.2, ContinuousLinearMap.comp_zero]
    have hcoordzero' :
        fderiv ℝ (fun q : LoopPlane => u (D q)) p = 0 := by
      have heq : (fun q : LoopPlane => c (A.map q)) = (fun q => u (D q)) :=
        funext hcoord
      change fderiv ℝ (fun q : LoopPlane => c (A.map q)) p = 0 at hcoordzero
      rw [heq] at hcoordzero
      exact hcoordzero
    have hDchain := M60.mfderiv_comp_continuousLinearEquiv
      (I := 𝓘(ℝ, E)) u D p
    rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv] at hDchain
    have hcompzero : (fderiv ℝ u (D p)).comp D.toContinuousLinearMap = 0 := by
      calc
        (fderiv ℝ u (D p)).comp D.toContinuousLinearMap =
            fderiv ℝ (fun q : LoopPlane => u (D q)) p := hDchain.symm
        _ = 0 := hcoordzero'
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, hw⟩ := D.surjective v
    have hv := congrArg (fun L : LoopPlane →L[ℝ] E => L w) hcompzero
    change fderiv ℝ u (D p) (D w) = 0 at hv
    rw [hw] at hv
    exact hv
  have hK : IsCompact (D '' m64AnnulusDomain) :=
    m64AnnulusDomain_isCompact.image D.continuous
  have hzero_finite :
      (m64PlaneDifferentialZeroSet u ∩ D '' m64AnnulusDomain).Finite := by
    exact m64PlaneHarmonicDifferential_zeroSet_finite_on_compact
      (O := (Set.univ : Set ℂ)) isOpen_univ isPreconnected_univ hu
      (fun z _ => hΓ z) (fun z _ => hsym z) (fun z _ => hτ z)
      (by rcases hnonconstant with ⟨x, y, hxy⟩
          exact ⟨x, mem_univ x, y, mem_univ y, hxy⟩)
      hK (by intro z hz; exact mem_univ z)
  apply (hzero_finite.image C).subset
  intro p hp
  refine ⟨D p, ⟨hbranch_to_zero p hp, ?_⟩, ?_⟩
  · exact ⟨p, interior_subset hp.1, rfl⟩
  · exact hCD p

end

end PoincareConjecture
