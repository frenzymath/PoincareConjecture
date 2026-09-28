import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.ComponentAssembly
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Surface
open Set MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem surface_sectional_lower_bound_of_orthonormal
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    {g : PoincareConjecture.RiemannianMetric 2 S} (D : PoincareConjecture.LeviCivitaData g)
    (x : S) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ u v : TangentSpace (𝓡 2) x,
      g.inner x u u = 1 → g.inner x v v = 1 → g.inner x u v = 0 →
        -K ≤ D.sectionalCurvature x u v) :
    ∀ u v : TangentSpace (𝓡 2) x, -K ≤ D.sectionalCurvature x u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hd : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 2)), finrank_euclideanSpace]
    simp
  let b : OrthonormalBasis (Fin 2) ℝ (TangentSpace (𝓡 2) x) :=
    (g.orthonormalBasis x).reindex (finCongr hd)
  have hb (i j : Fin 2) : g.inner x (b i) (b j) = if i = j then 1 else 0 :=
    b.inner_eq_ite i j
  have hp := hbound (b 0) (b 1) (by simp [hb]) (by simp [hb]) (by simp [hb])
  intro u v
  by_cases hz : g.inner x u u * g.inner x v v - (g.inner x u v)^2 = 0
  · rw [D.sectionalCurvature_eq_zero_of_gramDet_eq_zero x u v hz]
    linarith
  · rw [D.sectionalCurvature_eq_half_scalarCurvature x u v hz,
      D.scalarCurvature_eq_twice_sectionalCurvature x b]
    linarith

theorem PoincareConjecture.LeviCivitaData.integral_regularLevel_surface_pos_scalar_le
    {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : PoincareConjecture.RiemannianMetric 3 M} (D : PoincareConjecture.LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (t : ℝ) (hcompact : IsCompact (f ⁻¹' {t}))
    (hreg : ∀ x, f x = t → mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f x ≠ 0)
    {K : M → ℝ} (hKc : ContinuousOn K (g.regularDomain hf))
    (hK : ∀ x, f x = t → 0 ≤ K x)
    (hsec : ∀ x, f x = t → ∀ v w : TangentSpace (𝓡 3) x,
      -K x ≤ D.sectionalCurvature x v w)
    {β : ℝ} (hβ : 0 ≤ β)
    (hhess : ∀ x, f x = t → ∀ v : TangentSpace (𝓡 3) x,
      g.inner x (D.gradient f x) v = 0 →
        D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤ β * g.inner x v v)
    (N : ℕ) :
    let U := g.regularDomain hf
    let hr := g.regularDomain_regular hf
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf U hr 2 t
    letI := isManifold_openLevelSet hf U hr 2 t
    let L := openLevelSet f U t
    let gL := g.regularLevelMetric hf U hr t
    Nat.card (ConnectedComponents L) ≤ N →
    (∫ z, max 0 (gL.leviCivitaData.scalarCurvature z)
      ∂g.regularLevelVolume hf U hr t) ≤
      8 * Real.pi * (N : ℝ) + 2 *
        ∫ z, D.levelSectionalError f K β (openLevelIncl f U t z)
          ∂g.regularLevelVolume hf U hr t := by
  classical
  let U := g.regularDomain hf
  let hr := g.regularDomain_regular hf
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openLevelSetChartedSpace hf U hr 2 t
  let := isManifold_openLevelSet hf U hr 2 t
  let L := openLevelSet f U t
  let gL := g.regularLevelMetric hf U hr t
  let DL := gL.leviCivitaData
  let incl := openLevelIncl f U t
  let E := fun z : L => D.levelSectionalError f K β (incl z)
  dsimp only
  intro hcount
  have hsub : f ⁻¹' {t} ⊆ (U : Set M) :=
    fun x hx => (g.mem_regularDomain_iff hf x).mpr (hreg x hx)
  have hLc : IsCompact (univ : Set L) := by
    apply (isEmbedding_openLevelIncl f U t).isCompact_iff.mpr
    rw [image_univ, range_openLevelIncl, inter_eq_right.mpr hsub]
    exact hcompact
  let : CompactSpace L := isCompact_univ_iff.mp hLc
  have hEc : Continuous E :=
    (D.continuousOn_levelSectionalError_regularDomain hf hKc β).comp_continuous
      (contMDiff_openLevelIncl hf U hr 2 t).continuous (fun z => z.1.2)
  have hEn (z : L) : 0 ≤ E z :=
    D.levelSectionalError_nonneg f K hβ (hK (incl z) z.2)
  have hEs (z : L) : ∀ u v : TangentSpace (𝓡 2) z,
      -E z ≤ DL.sectionalCurvature z u v := by
    apply surface_sectional_lower_bound_of_orthonormal DL z (hEn z)
    intro u v hu hv huv
    have htan (w : TangentSpace (𝓡 2) z) :
        g.inner (incl z) (D.gradient f (incl z))
          (mfderiv (𝓡 2) (𝓡 3) incl z w) = 0 := by
      have hk : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f (incl z)
          (mfderiv (𝓡 2) (𝓡 3) incl z w) = 0 := by
        change mfderiv (𝓡 2) (𝓡 3) incl z w ∈
          (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f (incl z)).ker
        rw [← range_mfderiv_openLevelIncl hf U hr 2 t z]
        exact ⟨w, rfl⟩
      rw [D.inner_gradient]
      have hk' := congrArg (fun q => NormedSpace.fromTangentSpace (f (incl z)) q) hk
      convert hk' using 1 <;>
        simp only [mvfderiv, ContinuousLinearMap.coe_comp, Function.comp_apply, map_zero]; rfl
    have hs := D.regularLevel_sectionalCurvature_lower_bound (m := 1)
      hf U hr t (K (incl z)) β hβ DL z
      (fun a b _ _ _ => hsec (incl z) z.2 a b)
      (fun w => hhess (incl z) z.2 _ (htan w)) u v hu hv huv
    change -(K (incl z) + (max 0 (-D.levelMeanCurvature f (incl z)) +
      (2:ℝ) * β) * β) ≤ DL.sectionalCurvature z u v
    norm_num at hs
    linarith only [hs]
  have hb := DL.integral_pos_scalarCurvature_surface_le_components hEc hEn hEs
  have hc : (Nat.card (ConnectedComponents L) : ℝ) ≤ N := by exact_mod_cast hcount
  have hb' := hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 8 * Real.pi)) le_rfl)
  exact hb'
