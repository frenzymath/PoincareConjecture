import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Synge.Displacement
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Synge.ParallelField
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Synge.Variation.PositiveCurvature

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle ENNReal

namespace PoincareConjecture.Synge

open ConnectionAlongCurve ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric 3 M}

omit [T3Space M] [PreconnectedSpace M] in
private theorem deriv_chart_eq_velocity {q : ℝ → M} {t : ℝ} {p : M}
    (hq : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) q t) (hp : q t = p) :
    deriv (fun s => extChartAt (𝓡 3) p (q s)) t =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 3) q t 1 := by
  have hc : MDifferentiableAt (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) p) (q t) := by
    rw [hp]
    exact mdifferentiableAt_extChartAt (mem_chart_source _ p)
  have hchain := mfderiv_comp t hc hq
  rw [mfderiv_eq_fderiv] at hchain
  have hv := congrArg (fun L => L (1 : ℝ)) hchain
  change (fderiv ℝ (fun s => extChartAt (𝓡 3) p (q s)) t) 1 =
    mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) p) (q t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) q t 1) at hv
  rw [fderiv_eq_smul_deriv, one_smul] at hv
  have hid : ∀ v : TangentSpace (𝓡 3) (q t),
      mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) p) (q t) v = v := by
    rw [hp]
    intro v
    rw [mfderiv_extChartAt_self]
    rfl
  rw [hid] at hv
  exact hv

theorem not_minimum_displacement_of_negative_holonomy
    (D : LeviCivitaData g) (F : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ M)
    (hinner : ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
      g.inner x v w = g.inner (F x)
        (mfderiv (𝓡 3) (𝓡 3) F x v) (mfderiv (𝓡 3) (𝓡 3) F x w))
    {γ : ℝ → M} {ε : ℝ} (hε : 0 < ε)
    (hgeo : g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)))
    (hend : γ 1 = F (γ 0))
    (hpos : 0 < (g.edist (γ 0) (γ 1)).toReal)
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1))
    (hsec : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u v,
      g.inner (γ t) u u = 1 → g.inner (γ t) v v = 1 →
      g.inner (γ t) u v = 0 → 0 < D.sectionalCurvature (γ t) u v)
    (P : ℝ → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hi : ∀ t ∈ Icc (0 : ℝ) 1, (P t).IsInvertible)
    (hP : ∀ t ∈ Ioo (-ε) (1 + ε), ∀ u,
      ContDiffAt ℝ ∞ (chartField γ (γ t) (fun s => P s u)) t ∧
      manifoldCovDerivAlong g γ (fun s => P s u) 1 t = 0)
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u v,
      g.inner (γ t) (P t u) (P t v) = inner ℝ u v)
    (hdet : LinearMap.det (((P 1).inverse.comp
      ((mfderiv (𝓡 3) (𝓡 3) F (γ 0)).comp (P 0))).toLinearMap) < 0) :
    ¬ ∀ x : M, (g.edist (γ 0) (γ 1)).toReal ≤ (g.edist x (F x)).toReal := by
  intro hmin
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-ε) (1 + ε) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have h0 := hsub (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  have h1 := hsub (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  let L := (g.edist (γ 0) (γ 1)).toReal
  have hL : 0 < L := hpos
  have hd0 := (hgeo.contMDiffAt h0).mdifferentiableAt (by simp)
  have hvel0 := (hgeo.hasDerivAt_chart_at h0 (γ 0) (mem_extChartAt_source _)).1
  have hnorm := hgeo.initial_tangentNorm_eq_of_edist_segment hε rfl hvel0 hseg
  have hnorm0 : g.tangentNorm (γ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ 0 1) = L := by
    have hr := congrArg ENNReal.toReal hnorm
    rw [ENNReal.toReal_ofReal (show 0 ≤ g.tangentNorm (γ 0) _ from
      Real.sqrt_nonneg _), deriv_chart_eq_velocity hd0 rfl] at hr
    exact hr
  obtain ⟨C, hC⟩ := hgeo.exists_constant_tangentNorm (by linarith)
  have hCL : (C : ℝ) = L := (hC 0 h0).symm.trans hnorm0
  have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) = L :=
    (hC t (hsub ht)).trans hCL
  have hne (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1 ≠ 0 := by
    intro hz
    have hh := hspeed t ht
    simp only [RiemannianMetric.tangentNorm, hz, map_zero, Real.sqrt_zero] at hh
    exact hL.ne' hh.symm
  have hvelocity := g.endpoint_velocity_eq_of_minimum_displacement F hinner hε
    hgeo rfl hend (by simpa only [← hend] using hpos)
    (by simpa only [← hend] using hmin) (by simpa only [← hend] using hseg)
  obtain ⟨w, _, hmatch, hfield⟩ := exists_parallel_normal_field_of_negative_holonomy
    zero_lt_one isOpen_Ioo hgeo hsub P hi (fun t ht => hP t (hsub ht)) hp F hend
    (fun u v => (hinner (γ 0) u v).symm) hvelocity (hne 0 (by simp)) hdet
  let V := fun t => P t w
  have hV : ∀ t ∈ Ioo (-ε) (1 + ε),
      ContDiffAt ℝ ∞ (chartField γ (γ t) V) t := fun t ht => (hP t ht w).1
  have hind : ∀ t ∈ Icc (0 : ℝ) 1,
      LinearIndependent ℝ ![V t, mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1] := by
    intro t ht
    apply linearIndependent_fin2.mpr
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    refine ⟨hne t ht, ?_⟩
    intro r hr
    have hh := congrArg (fun z => g.inner (γ t) z (V t)) hr
    have horth : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) (V t) = 0 :=
      (hfield t ht).2.2.2
    simp only [map_smul, smul_apply, smul_eq_mul, horth, mul_zero] at hh
    exact (g.pos (γ t) (V t) (hfield t ht).2.2.1).ne' hh.symm
  obtain ⟨δ, hδ, _, η₀, hη₀, hη₀0, hη₀v⟩ :=
    g.exists_geodesic_initial_data (γ 0) (V 0)
  let η₁ := F ∘ η₀
  have hη₁ : g.IsGeodesicOn η₁ (Ioo (-δ) δ) :=
    hη₀.comp_local_isometry_manifold isOpen_univ F.contMDiff.contMDiffOn
      (fun x _ u v => hinner x u v) (fun _ _ => mem_univ _)
  have hη₁0 : η₁ 0 = γ 1 := by simp [η₁, hη₀0, hend]
  have hη₀d := (hη₀.contMDiffAt (show (0 : ℝ) ∈ Ioo (-δ) δ by
    constructor <;> linarith)).mdifferentiableAt (by simp)
  have hη₁d := (hη₁.contMDiffAt (show (0 : ℝ) ∈ Ioo (-δ) δ by
    constructor <;> linarith)).mdifferentiableAt (by simp)
  have hη₀velocity : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) η₀ 0 1 = V 0 :=
    (deriv_chart_eq_velocity hη₀d hη₀0).symm.trans hη₀v.deriv
  have hη₁velocity : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) η₁ 0 1 = V 1 := by
    have hh := congrArg (fun L => L (1 : ℝ))
      (mfderiv_comp 0 (F.mdifferentiable (by simp) (η₀ 0)) hη₀d)
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 3) η₁ 0 1 =
      mfderiv (𝓡 3) (𝓡 3) F (η₀ 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) η₀ 0 1) at hh
    rw [hη₀velocity, hη₀0] at hh
    exact hh.trans hmatch.symm
  have hη₁v : HasDerivAt (fun s => extChartAt (𝓡 3) (γ 1) (η₁ s)) (V 1) 0 := by
    have hd := (hη₁.hasDerivAt_chart_at (show (0 : ℝ) ∈ Ioo (-δ) δ by
      constructor <;> linarith) (γ 1) (by simp [hη₁0])).1
    rw [deriv_chart_eq_velocity hη₁d hη₁0, hη₁velocity] at hd
    exact hd
  apply not_minimizing_endpoints_of_parallel D zero_lt_one isOpen_Ioo hsub hgeo hV
    hsec (fun t ht => (hfield t ht).2.1) hind hδ hδ hη₀ hη₁ hη₀0 hη₁0
    hη₀v hη₁v hL hspeed
  apply Eventually.of_forall
  intro s
  simp only [sub_zero, one_mul]
  change ENNReal.ofReal L ≤ g.edist (η₀ s) (F (η₀ s))
  rw [ENNReal.ofReal_le_iff_le_toReal (g.edist_ne_top _ _)]
  exact hmin (η₀ s)

end PoincareConjecture.Synge
