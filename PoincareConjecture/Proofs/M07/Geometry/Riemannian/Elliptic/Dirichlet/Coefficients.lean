import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateEnergy
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff InnerProductSpace Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

def divergenceCoefficients (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) : ℝ :=
  g.pullbackVolumeDensity e x *
    EuclideanSpace.proj i ((g.pullbackCoefficients e x).inverse (EuclideanSpace.proj j))

theorem contDiffOn_divergenceCoefficients
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun x => divergenceCoefficients g e x i j) e.source := by
  intro x hx
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hef := he.contMDiffAt (e.open_source.mem_nhds hx)
  have hinv := g.isInvertible_pullbackCoefficients (hD.mfderiv_injective hx)
  have hI := hinv.contDiffAt_map_inverse.comp x (g.contDiffAt_pullbackCoefficients hef)
  have hentry := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp x
    (hI.clm_apply (contDiffAt_const (c := EuclideanSpace.proj (𝕜 := ℝ) j)))
  exact ((g.contDiffAt_pullbackVolumeDensity hef (hD.mfderiv_injective hx)).1.mul
    hentry).contDiffWithinAt

theorem divergenceCoefficients_symm
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) (i j : Fin n) :
    divergenceCoefficients g e x i j = divergenceCoefficients g e x j i := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hinv := g.isInvertible_pullbackCoefficients (hD.mfderiv_injective hx)
  let B := g.pullbackCoefficients e x
  have hsymm : B (B.inverse (EuclideanSpace.proj i)) (B.inverse (EuclideanSpace.proj j)) =
      B (B.inverse (EuclideanSpace.proj j)) (B.inverse (EuclideanSpace.proj i)) :=
    g.symm (e x) _ _
  rw [hinv.self_apply_inverse, hinv.self_apply_inverse] at hsymm
  exact congrArg (g.pullbackVolumeDensity e x * ·) hsymm

private theorem covector_apply_eq_sum
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    L v = ∑ i, L (EuclideanSpace.single i 1) * v i := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, mul_comm] using h.symm

private theorem covector_eq_sum_proj (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    L = ∑ i, L (EuclideanSpace.single i 1) • EuclideanSpace.proj i := by
  ext v
  simpa using covector_apply_eq_sum L v

theorem sum_divergenceCoefficients_eq_inverse_pairing
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (x : EuclideanSpace ℝ (Fin n))
    (F H : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    (∑ i, ∑ j, divergenceCoefficients g e x i j *
      F (EuclideanSpace.single j 1) * H (EuclideanSpace.single i 1)) =
      g.pullbackVolumeDensity e x * H ((g.pullbackCoefficients e x).inverse F) := by
  rw [covector_apply_eq_sum H, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  nth_rw 2 [covector_eq_sum_proj F]
  simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.mul_sum, divergenceCoefficients, PiLp.proj_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem divergenceCoefficients_pos
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    0 < ∑ i, ∑ j, divergenceCoefficients g e x i j * v i * v j := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hinj := hD.mfderiv_injective hx
  have hinv := g.isInvertible_pullbackCoefficients hinj
  let B := g.pullbackCoefficients e x
  let w := B.inverse (innerSL ℝ v)
  have hw : w ≠ 0 := by
    intro hzero
    have h := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v)
      (hinv.self_apply_inverse (innerSL ℝ v))
    change B w v = inner ℝ v v at h
    rw [hzero, map_zero, zero_apply] at h
    exact hv (inner_self_eq_zero.mp h.symm)
  have hAw : mfderiv (𝓡 n) (𝓡 n) e x w ≠ 0 := by
    intro hzero
    exact hw (hinj (by simpa using hzero))
  have hpos : 0 < B w w := g.pos (e x) _ hAw
  rw [show B w = innerSL ℝ v from hinv.self_apply_inverse (innerSL ℝ v)] at hpos
  have hsum := sum_divergenceCoefficients_eq_inverse_pairing (g := g) e x
    (innerSL ℝ v) (innerSL ℝ v)
  simp only [innerSL_apply_apply, EuclideanSpace.inner_single_right, starRingEnd_apply,
    star_trivial, one_mul]
    at hsum
  rw [show (∑ i, ∑ j, divergenceCoefficients g e x i j * v i * v j) =
      ∑ i, ∑ j, divergenceCoefficients g e x i j * v j * v i by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring, hsum]
  exact mul_pos (g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds hx)) hinj).2 hpos

theorem density_mul_inner_gradient_eq_sum_divergenceCoefficients
    {D : LeviCivitaData g} {Ω : Set M}
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (f h : EnergyTest D Ω) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) :
    g.pullbackVolumeDensity e x *
      g.inner (e x) (D.gradient f (e x)) (D.gradient h (e x)) =
      ∑ i, ∑ j, divergenceCoefficients g e x i j *
        fderiv ℝ (fun y => f (e y)) x (EuclideanSpace.single j 1) *
        fderiv ℝ (fun y => h (e y)) x (EuclideanSpace.single i 1) := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hinv := g.isInvertible_pullbackCoefficients (hD.mfderiv_injective hx)
  obtain ⟨w, hw⟩ := hD.mfderiv_surjective hx (D.gradient f (e x))
  have hF : g.pullbackCoefficients e x w = fderiv ℝ (fun y => f (e y)) x := by
    ext v
    rw [fderiv_comp_eq_inner_gradient e he f hx]
    change g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x w)
      (mfderiv (𝓡 n) (𝓡 n) e x v) = _
    rw [hw]
  rw [sum_divergenceCoefficients_eq_inverse_pairing, ← hF, hinv.inverse_apply_self,
    fderiv_comp_eq_inner_gradient e he h hx, hw, g.symm]

end PoincareConjecture.LeviCivitaData.Dirichlet
