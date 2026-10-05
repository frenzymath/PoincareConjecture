import PoincareLib.Geometry.Riemannian.Elliptic.Dirichlet.Coefficients
import PoincareLib.Analysis.Elliptic.Regularity.Coefficients
import PoincareLib.Geometry.Manifold.SmoothDomain

/-!
# Retained elliptic coefficients near the smooth boundary

The smooth metric and the retained volume produce uniformly elliptic
coefficient extensions in the constructed flattening coordinates.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace PoincareMT.LeviCivitaData.Dirichlet.Boundary

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem divergence_posDef (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source) :
    Matrix.PosDef (divergenceCoefficients g e x) := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, fun v hv => ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial] using divergenceCoefficients_symm (g := g) e he hei hx j i
  · let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
    have hw : w ≠ 0 := by
      intro h
      apply hv
      exact congrArg WithLp.ofLp h
    have hpos := divergenceCoefficients_pos (g := g) e he hei hx w hw
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum,
      w, WithLp.ofLp_toLp, mul_left_comm, mul_assoc] using hpos

private theorem contDiffOn_density (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (g.pullbackVolumeDensity e) e.source := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  intro x hx
  exact (g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds hx))
    (hD.mfderiv_injective hx)).1.contDiffWithinAt

/-- Boundary charts and neighborhoods can be fixed before the spectral
parameter when extending the retained elliptic coefficients. -/
theorem exists_local_elliptic_form [NeZero n] [T2Space M]
    (g : RiemannianMetric n M) {Ω : Set M}
    (S : Poincare.Manifold.SmoothDomain n Ω) (x : closure Ω) :
    ∃ (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
      (V : Set (EuclideanSpace ℝ (Fin n))),
      (x : M) ∈ e.target ∧ e.symm x ∈ V ∧ IsOpen V ∧
      IsCompact (closure V) ∧ closure V ⊆ e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      (∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0) ∧
      ∀ lambda : ℝ,
        ∃ B : Poincare.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm n univ,
          EqOn B.a (divergenceCoefficients g e) V ∧
          EqOn B.c (fun z => -lambda * g.pullbackVolumeDensity e z) V := by
  obtain ⟨e, hx, he, hei, hflat⟩ := S.exists_flattening_parametrization x
  obtain ⟨V, hV, hxV, hVc, hVs, B, hBA, hBρ⟩ :=
    Poincare.Analysis.Elliptic.exists_global_elliptic_extension e.open_source
      (isCompact_singleton (x := e.symm x))
      (singleton_subset_iff.mpr (e.map_target hx))
      (divergenceCoefficients g e) (g.pullbackVolumeDensity e)
      (contDiffOn_divergenceCoefficients e he hei)
      (fun z hz => divergence_posDef g e he hei hz) (contDiffOn_density g e he hei)
  refine ⟨e, V, hx, hxV (mem_singleton _), hV, hVc, hVs, he, hei,
    fun z hz => (hflat z hz).2.1, fun lambda => ?_⟩
  let Blambda : Poincare.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm n univ :=
    { B with
      c := fun z => -lambda * B.c z
      smooth_c := contDiff_const.mul B.smooth_c }
  refine ⟨Blambda, hBA, ?_⟩
  intro z hz
  exact congrArg (-lambda * ·) (hBρ hz)

end PoincareMT.LeviCivitaData.Dirichlet.Boundary
