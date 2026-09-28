import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue










set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology

universe u v w

namespace Diffeomorph

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]
  {H : Type v} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {K : Type w} [TopologicalSpace K] [ChartedSpace H K]
  [IsManifold I ∞ K]



theorem exists_fiberwise_of_deriv_pos
    (A : Diffeomorph I I K K ∞) (F : K × ℝ → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ F)
    (hpos : ∀ q : K, ∀ s : ℝ,
      0 < deriv (fun r : ℝ => F (q, r)) s)
    (hsurj : ∀ q : K, Function.Surjective (fun s : ℝ => F (q, s))) :
    ∃ D : Diffeomorph (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (K × ℝ) (K × ℝ) ∞,
      (∀ z : K × ℝ, D z = (A z.1, F z)) ∧
      (∀ z : K × ℝ,
        (D.symm z).1 = A.symm z.1 ∧ F (D.symm z) = z.2) := by
  classical
  have hmono (q : K) : StrictMono (fun s : ℝ => F (q, s)) :=
    strictMono_of_deriv_pos (hpos q)
  let G : K × ℝ → K × ℝ := fun z => (A z.1, F z)
  have hGinj : Injective G := by
    rintro ⟨q, s⟩ ⟨q', s'⟩ heq
    have hq : q = q' := A.injective (congrArg Prod.fst heq)
    subst q'
    have hs : s = s' := (hmono q).injective (congrArg Prod.snd heq)
    subst s'
    rfl
  have hGsurj : Surjective G := by
    rintro ⟨p, t⟩
    obtain ⟨s, hs⟩ := hsurj (A.symm p) t
    refine ⟨(A.symm p, s), ?_⟩
    simp [G, hs]
  let e : (K × ℝ) ≃ (K × ℝ) := Equiv.ofBijective G ⟨hGinj, hGsurj⟩
  have hinvf (y : K × ℝ) : (e.symm y).1 = A.symm y.1 := by
    have hy := congrArg Prod.fst (e.apply_symm_apply y)
    change A (e.symm y).1 = y.1 at hy
    apply A.injective
    simpa using hy
  have hinvh (y : K × ℝ) : F (e.symm y) = y.2 := by
    exact congrArg Prod.snd (e.apply_symm_apply y)
  have hforward : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ e :=
    (A.contMDiff.comp contMDiff_fst).prodMk hF
  have hinverse : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ e.symm := by
    intro y
    let q₀ : K := A.symm y.1
    let s₀ : ℝ := (e.symm y).2
    have hepair : e.symm y = (q₀, s₀) := Prod.ext (hinvf y) rfl
    have hzero : F (q₀, s₀) = y.2 := by
      rw [← hepair]
      exact hinvh y
    let c : PartialEquiv K E := extChartAt I q₀
    let x₀ : E := c q₀
    have hcsource : q₀ ∈ c.source := mem_extChartAt_source q₀
    have hctarget : x₀ ∈ c.target := mem_extChartAt_target q₀
    have hcsymm : c.symm x₀ = q₀ := c.left_inv hcsource
    have hcInv : ContMDiffAt 𝓘(ℝ, E) I ∞ c.symm x₀ :=
      (contMDiffOn_extChartAt_symm (I := I) (n := ∞) q₀ x₀ hctarget).contMDiffAt
        ((isOpen_extChartAt_target (I := I) q₀).mem_nhds hctarget)
    let u₀ : (E × ℝ) × ℝ := ((x₀, y.2), s₀)
    let Phi : (E × ℝ) × ℝ → ℝ := fun z => F (c.symm z.1.1, z.2) - z.1.2
    have hx : ContMDiffAt 𝓘(ℝ, (E × ℝ) × ℝ) 𝓘(ℝ, E) ∞
        (fun z : (E × ℝ) × ℝ => z.1.1) u₀ :=
      (contDiff_fst.fst : ContDiff ℝ ∞
        (fun z : (E × ℝ) × ℝ => z.1.1)).contMDiff.contMDiffAt
    have hs : ContMDiffAt 𝓘(ℝ, (E × ℝ) × ℝ) 𝓘(ℝ, ℝ) ∞
        (fun z : (E × ℝ) × ℝ => z.2) u₀ :=
      contDiff_snd.contMDiff.contMDiffAt
    have ht : ContMDiffAt 𝓘(ℝ, (E × ℝ) × ℝ) 𝓘(ℝ, ℝ) ∞
        (fun z : (E × ℝ) × ℝ => z.1.2) u₀ :=
      (contDiff_fst.snd : ContDiff ℝ ∞
        (fun z : (E × ℝ) × ℝ => z.1.2)).contMDiff.contMDiffAt
    have hPhi : ContDiffAt ℝ ∞ Phi u₀ :=
      (hF.contMDiffAt.comp u₀ ((hcInv.comp u₀ hx).prodMk hs)).contDiffAt.sub ht.contDiffAt
    let d : ℝ := deriv (fun s : ℝ => F (q₀, s)) s₀
    have hd : d ≠ 0 := ne_of_gt (hpos q₀ s₀)
    let L : ℝ →L[ℝ] ℝ :=
      fderiv ℝ Phi u₀ ∘L ContinuousLinearMap.inr ℝ (E × ℝ) ℝ
    have hLone : L 1 = d := by
      have hcomp := (hPhi.differentiableAt (by simp)).hasFDerivAt.comp s₀
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) (x₀, y.2) s₀)
      have hcomp' := hcomp.hasDerivAt
      change HasDerivAt (fun s : ℝ => Phi ((x₀, y.2), s)) (L 1) s₀ at hcomp'
      have hscalar : HasDerivAt (fun s : ℝ => F (q₀, s) - y.2) d s₀ :=
        (differentiableAt_of_deriv_ne_zero hd).hasDerivAt.sub_const y.2
      have hcomp'' : HasDerivAt (fun s : ℝ => F (q₀, s) - y.2) (L 1) s₀ := by
        simpa only [Phi, hcsymm] using hcomp'
      exact hcomp''.unique hscalar
    have hLapply (v : ℝ) : L v = d * v := by
      calc
        L v = v * L 1 := by simpa using L.map_smul v (1 : ℝ)
        _ = d * v := by rw [hLone, mul_comm]
    let Linv : ℝ →L[ℝ] ℝ := d⁻¹ • ContinuousLinearMap.id ℝ ℝ
    have hLright : L ∘L Linv = ContinuousLinearMap.id ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro v
      simp [Linv, hLapply, hd]
    have hLleft : Linv ∘L L = ContinuousLinearMap.id ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro v
      simp [Linv, hLapply, hd]
    have hLI : L.IsInvertible :=
      ContinuousLinearMap.IsInvertible.of_inverse hLright hLleft
    have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    let psi : E × ℝ → ℝ := hPhi.implicitFunction hn hLI
    have hpsi : ContDiffAt ℝ ∞ psi (x₀, y.2) :=
      hPhi.contDiffAt_implicitFunction hn hLI
    let P : K × ℝ → E × ℝ := fun z => (c (A.symm z.1), z.2)
    have hA : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) I ∞
        (fun z : K × ℝ => A.symm z.1) y :=
      A.symm.contMDiffAt.comp y contMDiffAt_fst
    have hc : ContMDiffAt I 𝓘(ℝ, E) ∞ c q₀ :=
      contMDiffAt_extChartAt
    have hP : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E × ℝ) ∞ P y :=
      (hc.comp y hA).prodMk_space contMDiffAt_snd
    let B : K × ℝ → K × ℝ := fun z => (A.symm z.1, psi (P z))
    have hB : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞ B y :=
      hA.prodMk (hpsi.contMDiffAt.comp y hP)
    have heq : ∀ᶠ z in 𝓝 y, G (B z) = z := by
      have hsource : ∀ᶠ z in 𝓝 y, A.symm z.1 ∈ c.source :=
        hA.continuousAt.eventually
          ((isOpen_extChartAt_source (I := I) q₀).mem_nhds hcsource)
      have hequation : ∀ᶠ z in 𝓝 y, Phi (P z, psi (P z)) = Phi u₀ :=
        hP.continuousAt.eventually (hPhi.eventually_apply_implicitFunction hn hLI)
      filter_upwards [hsource, hequation] with z hz hzeq
      apply Prod.ext
      · simp [G, B]
      · change F (A.symm z.1, psi (P z)) = z.2
        have hlocal : F (c.symm (c (A.symm z.1)), psi (P z)) - z.2 = 0 := by
          simpa only [Phi, u₀, P, hcsymm, hzero, sub_self] using hzeq
        rw [c.left_inv hz] at hlocal
        exact sub_eq_zero.mp hlocal
    have hagree : e.symm =ᶠ[𝓝 y] B := by
      filter_upwards [heq] with z hz
      apply e.injective
      exact (e.apply_symm_apply z).trans hz.symm
    exact hB.congr_of_eventuallyEq hagree
  refine ⟨{ toEquiv := e, contMDiff_toFun := hforward, contMDiff_invFun := hinverse },
    fun _ => rfl, ?_⟩
  intro z
  exact ⟨hinvf z, hinvh z⟩

end Diffeomorph

end
