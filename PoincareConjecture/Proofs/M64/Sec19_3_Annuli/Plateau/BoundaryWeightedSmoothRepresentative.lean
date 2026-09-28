import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeightedInteriorSmooth
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusContinuity












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain

local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace






theorem weighted_interior_smooth_representative
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hpos : ∀ q v, 0 ≤ Q q v v)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      Q q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) =
        g.inner q v v)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus) :
    ∃ W : M64ObservedWeakAnnulus (n := n) e c0 c1,
      ContMDiffOn (𝓡 2) (𝓡 n) ∞ W.map S ∧
      W.map =ᵐ[volume.restrict S] A.map ∧ W.column = A.column ∧
      (∀ (B : M → E →L[ℝ] E →L[ℝ] ℝ) (r : ℝ),
        W.weightedEnergy B r = A.weightedEnergy B r) ∧
      ∀ V : M64ObservedWeakAnnulus (n := n) e c0 c1,
        W.weightedEnergy Q modulus ≤ V.weightedEnergy Q modulus := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨D, hD, hbound⟩ := M60.exists_uniform_mfderiv_bound g e he
  have hcoercive (q : M) (v : E)
      (hv : v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q)) :
      ‖v‖ ^ 2 ≤ D ^ 2 * Q q v v := by
    obtain ⟨w, rfl⟩ := hv
    have hnorm : ‖(show E from mfderiv (𝓡 n) (𝓡 m) e q w)‖ ≤ D * ‖w‖ := by
      rw [← norm_tangentSpace_vectorSpace (x := e q)]
      exact ((mfderiv (𝓡 n) (𝓡 m) e q).le_opNorm w).trans
        (mul_le_mul_of_nonneg_right (hbound q) (norm_nonneg w))
    have hnormsq : ‖w‖ ^ 2 = g.inner q w w := (real_inner_self_eq_norm_sq w).symm
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD (norm_nonneg w))).mpr hnorm
    simpa only [mul_pow, hnormsq, hdiag] using hsq
  obtain ⟨W, hW, hae, hcol, henergy, hminW⟩ := A.weighted_continuous_representative
    g he hei hread Q hQ hpos (sq_nonneg D) hcoercive hmodulus hmin
  obtain ⟨C, hC⟩ := (isCompact_range hQ).isBounded.exists_norm_le
  have hsm := W.contMDiffOn_of_weightedEnergy_minimum g he hei.isEmbedding hread
    Q hQ (fun q => hC _ (mem_range_self q)) hdiag hmodulus hminW hW
  exact ⟨W, hsm, hae, hcol, henergy, hminW⟩

end PoincareConjecture.M64ObservedWeakAnnulus
