import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerLipschitzEmbedding
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerLipschitzTrace
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.CompetitorEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Complex
open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture

set_option maxHeartbeats 1600000 in

theorem m65SpanningDisk_weak_member
    {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (compact : IsCompact (univ : Set M)) {γ : C1FreeLoopSpace (M := M)}
    (D : LipschitzSpanningDisk g γ) :
    ∃ G : M65WeakDisk e γ, G.value = D.map ∧
      G.parameter = ⟨D.reparameterization.map, D.reparameterization.continuous_map⟩ ∧
      G.energy g = ∫ z in loopDiskSet, m60EnergyDensity g D.map z := by
  classical
  let mu : Measure LoopPlane := volume.restrict loopDiskSet
  let f := e ∘ D.map
  let B := EuclideanSpace.basisFun (Fin 2) ℝ
  obtain ⟨C, hLip⟩ := m65SpanningDisk_embedded_lipschitz g e he hinj compact D
  have hscalar (j : Fin N) := m65LipschitzOn_diskWeakTrace
    ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).lipschitz.comp_lipschitzOnWith
      hLip)
  choose u d b hu hd hb htrace using hscalar
  have hdiff : ∀ᵐ z ∂mu, DifferentiableAt ℝ f z := by
    filter_upwards [ae_restrict_of_ae D.ae_manifold_differentiable,
      ae_restrict_mem measurableSet_closedBall] with z hz hzs
    exact ((he.mdifferentiableAt (by simp)).comp z (hz hzs)).differentiableAt
  have hgrad (j : Fin N) (i : Fin 2) : d j i =ᵐ[mu]
      fun z => (fderiv ℝ f z (B i)) j := by
    filter_upwards [hd j i, hdiff] with z hz hdf
    rw [hz]
    have hh := ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ).hasFDerivAt.comp
      z hdf.hasFDerivAt).fderiv
    change fderiv ℝ ((EuclideanSpace.proj j) ∘ f) z (B i) = _
    rw [hh]
    rfl
  have hf : MemLp f 2 mu := MemLp.of_eval_piLp fun j => (Lp.memLp (u j)).ae_eq (hu j)
  have hdv (i : Fin 2) : MemLp (fun z => fderiv ℝ f z (B i)) 2 mu :=
    MemLp.of_eval_piLp fun j => (Lp.memLp (d j i)).ae_eq (hgrad j i)
  let U := hf.toLp f
  let V (i : Fin 2) := (hdv i).toLp (fun z => fderiv ℝ f z (B i))
  have hU (j : Fin N) : m65DiskCoordinateL2 U j = u j := by
    apply Lp.ext
    filter_upwards [m65DiskCoordinateL2_coe U j, hf.coeFn_toLp, hu j] with z hz hfz huj
    rw [hz, hfz, huj]
    rfl
  have hV (j : Fin N) (i : Fin 2) : m65DiskCoordinateL2 (V i) j = d j i := by
    apply Lp.ext
    filter_upwards [m65DiskCoordinateL2_coe (V i) j, (hdv i).coeFn_toLp,
      hgrad j i] with z hz hvz hdj
    rw [hz, hvz, hdj]
  let β : C(LoopCircle, LoopCircle) :=
    ⟨D.reparameterization.map, D.reparameterization.continuous_map⟩
  let H : LoopCircle ≃ₜ LoopCircle := {
    toFun := D.reparameterization.map
    invFun := D.reparameterization.inverse
    left_inv := D.reparameterization.left_inverse
    right_inv := D.reparameterization.right_inverse
    continuous_toFun := D.reparameterization.continuous_map
    continuous_invFun := D.reparameterization.continuous_inverse }
  have hβ : M65WeakCircleParameter β := subset_closure ⟨H, rfl⟩
  let Γ (j : Fin N) : C(LoopCircle, ℝ) :=
    ⟨fun z => e (γ (β z)) j,
      (EuclideanSpace.proj j).continuous.comp (he.continuous.comp
        (γ.continuous.comp β.continuous))⟩
  choose b0 hb0 using fun j => m65CircleBoundary_continuous_class (Γ j)
  have hboundary (j : Fin N) : b j = m65CircleBoundaryPullback (b0 j) := by
    apply Lp.ext
    filter_upwards [hb j, hb0 j] with t ht h0
    rw [ht, h0]
    change e (D.map (Proofs.M58.angularPoint t)) j =
      e (γ (D.reparameterization.map
        ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩)) j
    rw [D.boundary_eq ⟨Proofs.M58.angularPoint t, Proofs.M58.norm_angularPoint t⟩]
  let G : M65WeakDisk e γ := {
    value := D.map
    embeddedValue := U
    embeddedValue_ae := hf.coeFn_toLp
    derivative := V
    parameter := β
    weakly_monotone := hβ
    boundary := b0
    boundary_ae := hb0
    weak_trace := by
      intro j
      rw [hU j]
      simp_rw [hV j]
      rw [← hboundary j]
      exact htrace j }
  refine ⟨G, rfl, rfl, ?_⟩
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae D.ae_manifold_differentiable,
    ae_restrict_mem measurableSet_closedBall, ae_all_iff.mpr (fun i => (hdv i).coeFn_toLp)]
      with z hdf hzs hVz
  have hchain (i : Fin 2) : V i z = mfderiv (𝓡 3) (𝓡 N) e (D.map z)
      (mfderiv (𝓡 2) (𝓡 3) D.map z (B i)) := by
    rw [hVz i]
    change fderiv ℝ (e ∘ D.map) z (B i) = _
    rw [← mfderiv_eq_fderiv, mfderiv_comp z (he.mdifferentiableAt (by simp)) (hdf hzs)]
    rfl
  change (1 / 2 : ℝ) * ∑ i, m65EmbeddingMetric g e (D.map z) (V i z) (V i z) =
    (1 / 2 : ℝ) * ∑ i, g.inner (D.map z)
      (mfderiv (𝓡 2) (𝓡 3) D.map z (B i)) (mfderiv (𝓡 2) (𝓡 3) D.map z (B i))
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hchain i, m65EmbeddingMetric_image g e (D.map z) (hinj (D.map z))]

end PoincareConjecture
