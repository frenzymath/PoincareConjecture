import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteMotionEnergyIntegral





noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "Z" => EuclideanSpace ℝ (Fin (d + 3))





def m64BoundaryMotionParameters (e : M → E) (f : LoopPlane → M)
    (sigma0 sigma1 : ℝ → ℝ) (p : LoopPlane) : Z :=
  EuclideanSpace.finAddEquivProd.symm
    (e (f p), !₂[sigma0 (p 0), sigma1 (p 0), p 1])





theorem m64BoundaryMotionParameters_contDiffOn {e : M → E}
    (he : ContMDiff (𝓡 n) (𝓡 d) ∞ e) {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f m64AnnulusDomain)
    {sigma0 sigma1 : ℝ → ℝ} (hsigma0 : ContDiff ℝ 1 sigma0)
    (hsigma1 : ContDiff ℝ 1 sigma1) :
    ContDiffOn ℝ 1 (m64BoundaryMotionParameters e f sigma0 sigma1) m64AnnulusDomain := by
  have hobs : ContDiffOn ℝ 1 (e ∘ f) m64AnnulusDomain :=
    ((he.of_le (by simp)).comp_contMDiffOn hf).contDiffOn
  have hlabels : ContDiff ℝ 1 (fun p : LoopPlane =>
      (!₂[sigma0 (p 0), sigma1 (p 0), p 1] : EuclideanSpace ℝ (Fin 3))) := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · change ContDiff ℝ 1 (fun p : LoopPlane => sigma0 (p 0))
      fun_prop
    · change ContDiff ℝ 1 (fun p : LoopPlane => sigma1 (p 0))
      fun_prop
    · change ContDiff ℝ 1 (fun p : LoopPlane => p 1)
      fun_prop
  exact EuclideanSpace.finAddEquivProd.symm.contDiff.comp_contDiffOn
    (hobs.prodMk hlabels.contDiffOn)





def m64BoundaryDisplacement (e : M → E) (c0 c1 : ℝ → ℝ → M)
    (w : ℝ × Z) : E :=
  let q := (EuclideanSpace.finAddEquivProd : Z ≃L[ℝ] E × EuclideanSpace ℝ (Fin 3)) w.2
  q.1 + (1 - q.2 2) • (e (c0 w.1 (q.2 0)) - e (c0 0 (q.2 0))) +
    q.2 2 • (e (c1 w.1 (q.2 1)) - e (c1 0 (q.2 1)))

omit [TopologicalSpace M] in




theorem m64BoundaryDisplacement_zero (e : M → E) (c0 c1 : ℝ → ℝ → M) (q : Z) :
    m64BoundaryDisplacement e c0 c1 (0, q) =
      (EuclideanSpace.finAddEquivProd q : E × EuclideanSpace ℝ (Fin 3)).1 := by
  simp only [m64BoundaryDisplacement, sub_self, smul_zero, add_zero]

omit [TopologicalSpace M] in




theorem m64BoundaryDisplacement_parameters (e : M → E) (c0 c1 : ℝ → ℝ → M)
    (f : LoopPlane → M) (sigma0 sigma1 : ℝ → ℝ) (s : ℝ) (p : LoopPlane) :
    m64BoundaryDisplacement e c0 c1 (s, m64BoundaryMotionParameters e f sigma0 sigma1 p) =
      e (f p) + (1 - p 1) • (e (c0 s (sigma0 (p 0))) - e (c0 0 (sigma0 (p 0)))) +
        p 1 • (e (c1 s (sigma1 (p 0))) - e (c1 0 (sigma1 (p 0)))) := by
  simp [m64BoundaryDisplacement, m64BoundaryMotionParameters]





theorem m64BoundaryDisplacement_contDiffOn {e : M → E}
    (he : ContMDiff (𝓡 n) (𝓡 d) ∞ e) {T : Set ℝ} (hzero : (0 : ℝ) ∈ T)
    (c0 c1 : ℝ → ℝ → M)
    (hc0 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (Function.uncurry c0) (T ×ˢ univ))
    (hc1 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞ (Function.uncurry c1) (T ×ˢ univ)) :
    ContDiffOn ℝ ∞ (m64BoundaryDisplacement e c0 c1) (T ×ˢ univ) := by
  let D : Z ≃L[ℝ] E × EuclideanSpace ℝ (Fin 3) := EuclideanSpace.finAddEquivProd
  have hbase : ContDiff ℝ ∞ (fun w : ℝ × Z => (D w.2).1) := by fun_prop
  have hcoord (i : Fin 3) : ContDiff ℝ ∞ (fun w : ℝ × Z => (D w.2).2 i) := by fun_prop
  have hpair (i : Fin 3) := (contDiff_fst.prodMk (hcoord i)).contMDiff
  have hpair0 (i : Fin 3) := ((contDiff_const (c := (0 : ℝ))).prodMk (hcoord i)).contMDiff
  have hmaps (i : Fin 3) : MapsTo (fun w : ℝ × Z => (w.1, (D w.2).2 i))
      (T ×ˢ univ) (T ×ˢ univ) := fun _ hw => ⟨hw.1, mem_univ _⟩
  have hmaps0 (i : Fin 3) : MapsTo (fun w : ℝ × Z => ((0 : ℝ), (D w.2).2 i))
      (T ×ˢ univ) (T ×ˢ univ) := fun _ _ => ⟨hzero, mem_univ _⟩
  have h00 := (he.comp_contMDiffOn (hc0.comp (hpair 0).contMDiffOn (hmaps 0))).contDiffOn
  have h01 := (he.comp_contMDiffOn (hc0.comp (hpair0 0).contMDiffOn (hmaps0 0))).contDiffOn
  have h10 := (he.comp_contMDiffOn (hc1.comp (hpair 1).contMDiffOn (hmaps 1))).contDiffOn
  have h11 := (he.comp_contMDiffOn (hc1.comp (hpair0 1).contMDiffOn (hmaps0 1))).contDiffOn
  exact (hbase.contDiffOn.add
    ((contDiffOn_const.sub (hcoord 2).contDiffOn).smul (h00.sub h01))).add
      ((hcoord 2).contDiffOn.smul (h10.sub h11))

end PoincareConjecture
