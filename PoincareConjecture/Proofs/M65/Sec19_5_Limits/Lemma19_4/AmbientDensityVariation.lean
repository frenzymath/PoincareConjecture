import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.MovingDensityVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m65AreaGram_det_comp_eq_zero (g₀ g : RiemannianMetric n M)
    {f : LoopPlane → M} {φ : M → M} {z : LoopPlane}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f z)
    (hφ : MDifferentiableAt (𝓡 n) (𝓡 n) φ (f z))
    (hzero : (m60AreaGram g₀ f z).det = 0) :
    (m60AreaGram g (φ ∘ f) z).det = 0 := by
  by_contra hne
  have hlin := (m65AreaGram_det_ne_zero_iff g (φ ∘ f) z).mp hne
  have hlin' : LinearIndependent ℝ
      (fun i : Fin 2 => mfderiv (𝓡 n) (𝓡 n) φ (f z)
        (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ i))) := by
    rw [mfderiv_comp z hφ hf] at hlin
    exact hlin
  exact ((m65AreaGram_det_ne_zero_iff g₀ f z).mpr
    (LinearIndependent.of_comp (mfderiv (𝓡 n) (𝓡 n) φ (f z)).toLinearMap hlin')) hzero

variable {a b : ℝ} (F : RicciFlow n M (Icc a b))

theorem m65AmbientAreaDensity_hasDerivAt_zero
    (φ : ℝ → M → M) {f : LoopPlane → M} {z : LoopPlane} {t : ℝ}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f z)
    (hφ : ∀ᶠ s in 𝓝 t, MDifferentiableAt (𝓡 n) (𝓡 n) (φ s) (f z))
    (hzero : (m60AreaGram (F.metric t) f z).det = 0) :
    HasDerivAt (fun s => m60AreaDensity (F.metric s) (φ s ∘ f) z) 0 t := by
  apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [hφ] with s hs
  simp only [m60AreaDensity,
    m65AreaGram_det_comp_eq_zero (F.metric t) (F.metric s) hf hs hzero,
    max_self, Real.sqrt_zero]

theorem m65AmbientAreaDensity_hasDerivAt
    (φ : ℝ → M → M) {f : LoopPlane → M} {z : LoopPlane} {t : ℝ}
    (ht : t ∈ Ioo a b) (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f z)
    (hφ : ∀ᶠ s in 𝓝 t, MDifferentiableAt (𝓡 n) (𝓡 n) (φ s) (f z))
    (hinj : Function.Injective (mfderiv (𝓡 n) (𝓡 n) (φ t) (f z)))
    (hu : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) (fun s => φ s (f z)) t)
    (hcol : ∀ i : Fin 2, MDifferentiableAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n))
      (fun s => (⟨φ s (f z), mfderiv (𝓡 2) (𝓡 n) (φ s ∘ f) z
        (EuclideanSpace.basisFun (Fin 2) ℝ i)⟩ : TangentBundle (𝓡 n) M)) t) :
    HasDerivAt (fun s => m60AreaDensity (F.metric s) (φ s ∘ f) z)
      (-m65PlaneRicciTraceDensity (F.connection t) (φ t ∘ f) z +
        m65PlaneMotionDensity F (fun s => φ s ∘ f) t z) t := by
  have hφt := hφ.self_of_nhds
  by_cases hzero : (m60AreaGram (F.metric t) f z).det = 0
  · have hzero' := m65AreaGram_det_comp_eq_zero (F.metric t) (F.metric t) hf hφt hzero
    simpa only [m65PlaneRicciTraceDensity, m65PlaneMotionDensity, hzero', if_pos,
      neg_zero, zero_add] using m65AmbientAreaDensity_hasDerivAt_zero F φ hf hφ hzero
  · have hlin := (m65AreaGram_det_ne_zero_iff (F.metric t) f z).mp hzero
    have hlin' := hlin.map' (mfderiv (𝓡 n) (𝓡 n) (φ t) (f z)).toLinearMap
      (LinearMap.ker_eq_bot.mpr hinj)
    have hne : (m60AreaGram (F.metric t) (φ t ∘ f) z).det ≠ 0 := by
      apply (m65AreaGram_det_ne_zero_iff (F.metric t) (φ t ∘ f) z).mpr
      rw [mfderiv_comp z hφt hf]
      exact hlin'
    exact m65MovingAreaDensity_hasDerivAt F (fun s => φ s ∘ f) z ht hu hcol
      (lt_of_le_of_ne (m65AreaGram_det_nonneg (F.metric t) (φ t ∘ f) z) hne.symm)

set_option maxHeartbeats 1000000 in

theorem m65AmbientAreaDensity_hasDerivAt_of_contMDiffAt
    (φ : ℝ → M → M) {f : LoopPlane → M} {z : LoopPlane} {t : ℝ}
    (ht : t ∈ Ioo a b) (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f z)
    (hφ : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 n) 2
      (Function.uncurry φ) (t, f z))
    (hinj : Function.Injective (mfderiv (𝓡 n) (𝓡 n) (φ t) (f z))) :
    HasDerivAt (fun s => m60AreaDensity (F.metric s) (φ s ∘ f) z)
      (-m65PlaneRicciTraceDensity (F.connection t) (φ t ∘ f) z +
        m65PlaneMotionDensity F (fun s => φ s ∘ f) t z) t := by
  have htime : ContinuousAt (fun s : ℝ => (s, f z)) t :=
    continuousAt_id.prodMk continuousAt_const
  have hnear : ∀ᶠ s in 𝓝 t,
      ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) (𝓡 n) 2
        (Function.uncurry φ) (s, f z) :=
    htime.eventually ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hφ)
  have hspatial : ∀ᶠ s in 𝓝 t, MDifferentiableAt (𝓡 n) (𝓡 n) (φ s) (f z) := by
    filter_upwards [hnear] with s hs
    exact (hs.comp (f z) (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt
      (by decide)
  have hbase : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) 1 (fun s => φ s (f z)) t :=
    (hφ.of_le (by norm_num)).comp t (contMDiffAt_id.prodMk contMDiffAt_const)
  apply m65AmbientAreaDensity_hasDerivAt F φ ht hf hspatial hinj
    (hbase.mdifferentiableAt (by decide))
  intro i
  let v : TangentSpace (𝓡 n) (f z) :=
    mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hcoord := hφ.mfderiv φ (fun _ : ℝ => f z) (m := 1)
    contMDiffAt_const (by norm_num)
  have hv : ContMDiffAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) 1
      (fun _ : ℝ => (⟨f z, v⟩ : TangentBundle (𝓡 n) M)) t := contMDiffAt_const
  have hcolumn : ContMDiffAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) 1
      (fun s => (⟨φ s (f z), mfderiv (𝓡 n) (𝓡 n) (φ s) (f z) v⟩ :
        TangentBundle (𝓡 n) M)) t :=
    ContMDiffAt.clm_apply_of_inCoordinates
      (IB₁ := 𝓡 n) (IB₂ := 𝓡 n) (IM := 𝓘(ℝ, ℝ))
      (E₁ := TangentSpace (𝓡 n)) (E₂ := TangentSpace (𝓡 n))
      (b₁ := fun _ : ℝ => f z) (b₂ := fun s => φ s (f z))
      (ϕ := fun s => mfderiv (𝓡 n) (𝓡 n) (φ s) (f z))
      (v := fun _ => v) hcoord hv hbase
  apply (hcolumn.mdifferentiableAt (by decide)).congr_of_eventuallyEq
  filter_upwards [hspatial] with s hs
  rw [mfderiv_comp z hs hf]
  rfl

end PoincareConjecture
