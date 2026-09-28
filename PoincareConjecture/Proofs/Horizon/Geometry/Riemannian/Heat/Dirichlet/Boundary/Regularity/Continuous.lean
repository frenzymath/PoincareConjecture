import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.HeatFlow
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Embedding.Continuous
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Embedding.SmoothRepresentative








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

open Poincare.Analysis.Sobolev

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}

local notation "E" => EuclideanSpace ℝ (Fin n)



theorem exists_local_heatPower_continuous (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (x : closure Ω) :
    ∃ (e : OpenPartialHomeomorph E M) (χ : M → ℝ) (V : Set E),
      (x : M) ∈ e.target ∧ e.symm x ∈ V ∧ IsOpen V ∧
      IsCompact (closure V) ∧ closure V ⊆ e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ e.target ∧ (∀ z ∈ V, χ (e z) = 1) ∧
      (∀ z ∈ e.source, e z ∈ Ω ↔ 0 < z 0) ∧
      ∀ (k : ℕ) (t : ℝ), 0 < t → ∀ f : Lp ℝ 2 (g.volumeMeasure.restrict Ω),
        ∃ F : E → ℝ,
          Continuous F ∧ ContDiffOn ℝ ∞ F (V ∩ {z : E | 0 < z 0}) ∧
          (chartPullback e (fun y => χ y * toL2 D Ω
            (energyHeatSpectralPower D Ω (Nat.pos_of_ne_zero (NeZero.ne n))
              S.isOpen S.isCompact_closure k t f) y)
            =ᵐ[volume.restrict (V ∩ {z : E | 0 < z 0})] F) ∧
          ∀ z : E, z 0 ≤ 0 → F z = 0 := by
  obtain ⟨e, χ, W, hx, hxW, hW, hWc, hWs, he, hei, hχ, hc, hs, hone, hflat, hreg⟩ :=
    exists_local_heatPower_memWkp D S x
  obtain ⟨V, hV, hxV, hVW, hVc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm x)) hW (singleton_subset_iff.mpr hxW)
  obtain ⟨ψ, hψ, hψc, _, hψone, hψs⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff hVc hW hVW
  have hVW' : V ⊆ W := subset_closure.trans hVW
  refine ⟨e, χ, V, hx, hxV (mem_singleton _), hV, hVc,
    hVW.trans (subset_closure.trans hWs), he, hei, hχ, hc, hs,
    fun z hz => hone z (hVW' hz), hflat, ?_⟩
  intro k t ht f
  let hn := Nat.pos_of_ne_zero (NeZero.ne n)
  let u := energyHeatSpectralPower D Ω hn S.isOpen S.isCompact_closure k t f
  let U := chartPullback e (fun y => χ y * toL2 D Ω u y)
  let H : Set E := {z | 0 < z 0}
  have hH : IsOpen H := BoundaryTangential.isOpen_halfSpace
  have hVH : IsOpen (V ∩ H) := hV.inter hH
  have hu0 : Weak.MemW01p 2 U H := memW01p_chartPullback_toL2 e he hei χ hχ hc hs hflat u
  have hw0 := BoundaryTangential.memW01p_mul_smooth hH hu0 hψ hψc
  have hwk := BoundaryLocalization.memWkp_mul_smooth_of_tsupport_subset (n + 1)
    hH hW (hreg (n + 1) k t ht f) hψ hψc hψs
  obtain ⟨F, hF, hUF, hzero⟩ := BoundaryEmbedding.exists_continuous_zero_extension
    hψc.mul_right hw0 hwk
  have hUFV : U =ᵐ[volume.restrict (V ∩ H)] F := by
    filter_upwards [ae_restrict_of_ae hUF, ae_restrict_mem hVH.measurableSet] with z hz hzV
    change H.indicator (ψ * U) z = F z at hz
    simpa only [indicator_of_mem hzV.2, Pi.mul_apply, hψone z (subset_closure hzV.1), one_mul] using hz
  have huV (r : ℕ) : Euclidean.MemWkp r 2 U (V ∩ H) :=
    (hreg r k t ht f).mono_set (by norm_num) hVH (inter_subset_inter_left _ hVW')
  obtain ⟨G, hG, hUG⟩ := EuclideanIteratedEmbedding.contDiffOn_of_forall_memWkp_two hVH huV
  have hFG : EqOn F G (V ∩ H) :=
    Measure.eqOn_open_of_ae_eq (hUFV.symm.trans hUG) hVH hF.continuousOn hG.continuousOn
  exact ⟨F, hF, hG.congr hFG, hUFV, hzero⟩

end PoincareConjecture.LeviCivitaData.Dirichlet.Boundary
