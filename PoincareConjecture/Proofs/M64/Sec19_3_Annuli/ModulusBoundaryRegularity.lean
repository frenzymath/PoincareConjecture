import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusBoundaryImmersion
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusEnergyDensity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64Annulus_slice_contMDiff
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    {O : Set LoopPlane} (hO : IsOpen O) (hdom : m64AnnulusDomain ⊆ O)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map O)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => A.map (annulusPoint x s)) := by
  have hline : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (fun x => annulusPoint x s) := by
    apply contMDiff_iff_contDiff.mpr
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun x : ℝ => x)
      exact contDiff_id
    · simpa [annulusPoint] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => s))
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hper : Function.Periodic (fun x => A.map (annulusPoint x s)) curvePeriod :=
    fun x => A.periodic x s
  intro x
  let z := -toIcoDiv hP 0 x
  let T := z • curvePeriod
  let y := toIcoMod hP 0 x
  have hy : y ∈ Ico (0 : ℝ) curvePeriod := toIcoMod_mem_Ico' hP x
  have hpoint : T + x = y := by
    simp [T, y, z, toIcoMod, neg_smul, sub_eq_add_neg, add_comm]
  have hyD : annulusPoint y s ∈ m64AnnulusDomain := ⟨hy.1, hy.2.le, hs.1, hs.2⟩
  have hlocal : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞
      (fun x => A.map (annulusPoint x s)) y :=
    (hA.contMDiffAt (hO.mem_nhds (hdom hyD))).comp y (hline y)
  have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞
      (fun q => A.map (annulusPoint (T + q) s)) x :=
    (hpoint.symm ▸ hlocal).comp x (contDiffAt_const.add contDiffAt_id).contMDiffAt
  have heq : (fun q => A.map (annulusPoint (T + q) s)) =
      (fun q => A.map (annulusPoint q s)) := by
    funext q
    simpa only [T, add_comm] using hper.zsmul z q
  simpa only [heq] using hcomp

theorem m64Annulus_modulusEnergyDensity_pos_of_horizontal_immersed
    (g : RiemannianMetric n M) {r : ℝ} (hr : 0 < r)
    {f : LoopPlane → M} {x s : ℝ}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f (annulusPoint x s))
    (himm : curveVelocity (n := n) (fun y => f (annulusPoint y s)) x ≠ 0) :
    0 < m64ModulusEnergyDensity g r f (annulusPoint x s) := by
  let u0 := mfderiv (𝓡 2) (𝓡 n) f (annulusPoint x s)
    (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  let u1 := mfderiv (𝓡 2) (𝓡 n) f (annulusPoint x s)
    (EuclideanSpace.basisFun (Fin 2) ℝ 1)
  have hvel : curveVelocity (n := n) (fun y => f (annulusPoint y s)) x = u0 := by
    simpa only [u0, EuclideanSpace.basisFun_apply] using m64Annulus_horizontal_velocity hf
  have hu0 : u0 ≠ 0 := fun h => himm (hvel.trans h)
  have hpos := mul_pos hr (g.pos (f (annulusPoint x s)) u0 hu0)
  have hnonneg : 0 ≤ r⁻¹ * g.inner (f (annulusPoint x s)) u1 u1 := by
    apply mul_nonneg (inv_nonneg.mpr hr.le)
    by_cases h : u1 = 0
    · simp [h]
    · exact (g.pos _ _ h).le
  change 0 < (r * g.inner (f (annulusPoint x s)) u0 u0 +
    r⁻¹ * g.inner (f (annulusPoint x s)) u1 u1) / 2
  linarith

end PoincareConjecture
