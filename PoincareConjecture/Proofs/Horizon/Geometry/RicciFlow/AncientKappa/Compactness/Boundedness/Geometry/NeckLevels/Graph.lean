import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.NeckLevels.Projection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.NeckLevels.ScalarGraph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace Filter
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem exists_smooth_level_graph
    (N : EpsilonNeck g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    {W m c : ℝ} (hW : 0 < W) (hWdom : W < N.epsilon⁻¹) (hm : 0 < m)
    (hderiv : ∀ (q : UnitTwoSphere) (t : ℝ), t ∈ Icc (-W) W →
      m ≤ |deriv (fun s : ℝ => f (N.coordinate_map (q, s))) t|)
    (hcenter : ∀ q : UnitTwoSphere, |f (N.coordinate_map (q, 0)) - c| < m * W) :
    ∃ h : UnitTwoSphere → ℝ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h ∧
      (∀ q, h q ∈ Ioo (-W) W) ∧
      (∀ q, f (N.coordinate_map (q, h q)) = c) ∧
      ContMDiff (𝓡 2) (𝓡 3) ∞ (fun q => N.coordinate_map (q, h q)) ∧
      {x | x ∈ N.region (-W) W ∧ f x = c} =
        range (fun q => N.coordinate_map (q, h q)) := by
  let U : Opens M := ⟨N.region (-W) W, N.isOpen_region (-W) W⟩
  have hdom {t : ℝ} (ht : t ∈ Icc (-W) W) :
      t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨(neg_lt_neg hWdom).trans_le ht.1, ht.2.trans_lt hWdom⟩
  have hcoord (q : UnitTwoSphere) {t : ℝ} (ht : t ∈ Icc (-W) W) :
      (q, t) ∈ N.cylinderDomain := ⟨mem_univ _, hdom ht⟩
  have hF (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Icc (-W) W) :
      ContDiffAt ℝ ∞ (fun s : ℝ => f (N.coordinate_map (q, s))) t := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact (hf _).comp t
      ((N.coordinate_map_smooth.contMDiffAt
        (N.cylinderDomain_open.mem_nhds (hcoord q ht))).comp t
          (contMDiffAt_const.prodMk contMDiffAt_id))
  have hroot (q : UnitTwoSphere) :
      ∃! t : ℝ, t ∈ Ioo (-W) W ∧ f (N.coordinate_map (q, t)) = c :=
    Poincare.Analysis.existsUnique_level_of_abs_deriv_ge hW hm
      (hF q) (hderiv q) (hcenter q)
  have haxial (x : M) (hx : x ∈ U) :
      mvfderiv (𝓡 3) f x
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
          N.coordinate_map (N.coordinate_inverse x) (0, 1)) ≠ 0 := by
    have hx' : x ∈ N.region (-W) W := hx
    have hz := N.coordinate_inverse_mem x hx'.1
    have hbound := hderiv (N.coordinate_inverse x).1 (N.coordinate_inverse x).2
      ⟨hx'.2.1.le, hx'.2.2.le⟩
    rw [(N.hasDerivAt_comp_axis hf (N.coordinate_inverse x).1 hz.2).deriv] at hbound
    have hpair : ((N.coordinate_inverse x).1, (N.coordinate_inverse x).2) =
        N.coordinate_inverse x := Prod.eta _
    rw [hpair, N.coordinate_map_coordinate_inverse hx'.1] at hbound
    intro heq
    exact (not_le_of_gt hm) (hbound.trans_eq ((congrArg abs heq).trans (abs_zero)))
  have hreg (x : M) (hx : x ∈ U) : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f x ≠ 0 := by
    intro heq
    apply haxial x hx
    simp only [mvfderiv, heq, ContinuousLinearMap.comp_zero, zero_apply]
  letI := openLevelSetChartedSpace hf U hreg 2 c
  letI := isManifold_openLevelSet hf U hreg 2 c
  let P : openLevelSet f U c → UnitTwoSphere :=
    fun z => (N.coordinate_inverse (openLevelIncl f U c z)).1
  have hPsmooth : ContMDiff (𝓡 2) (𝓡 2) ∞ P :=
    N.regularLevel_sphereProjection_contMDiff hf U (fun _ hx => hx.1) hreg c
  have hPderiv : ∀ z, Bijective (mfderiv (𝓡 2) (𝓡 2) P z) :=
    N.regularLevel_sphereProjection_bijective_mfderiv hf U
      (fun _ hx => hx.1) hreg c haxial
  have hPbij : Bijective P := by
    constructor
    · intro x y hxy
      have hx : openLevelIncl f U c x ∈ N.region (-W) W := x.1.2
      have hy : openLevelIncl f U c y ∈ N.region (-W) W := y.1.2
      have hxroot : (N.coordinate_inverse (openLevelIncl f U c x)).2 ∈ Ioo (-W) W ∧
          f (N.coordinate_map (P x, (N.coordinate_inverse (openLevelIncl f U c x)).2)) = c := by
        refine ⟨hx.2, ?_⟩
        rw [show (P x, (N.coordinate_inverse (openLevelIncl f U c x)).2) =
          N.coordinate_inverse (openLevelIncl f U c x) from rfl,
          N.coordinate_map_coordinate_inverse hx.1]
        exact x.2
      have hyroot : (N.coordinate_inverse (openLevelIncl f U c y)).2 ∈ Ioo (-W) W ∧
          f (N.coordinate_map (P x, (N.coordinate_inverse (openLevelIncl f U c y)).2)) = c := by
        refine ⟨hy.2, ?_⟩
        rw [hxy, show (P y, (N.coordinate_inverse (openLevelIncl f U c y)).2) =
          N.coordinate_inverse (openLevelIncl f U c y) from rfl,
          N.coordinate_map_coordinate_inverse hy.1]
        exact y.2
      have ht := (hroot (P x)).unique hxroot hyroot
      have hcoords : N.coordinate_inverse (openLevelIncl f U c x) =
          N.coordinate_inverse (openLevelIncl f U c y) := Prod.ext hxy ht
      apply Subtype.ext
      apply Subtype.ext
      change openLevelIncl f U c x = openLevelIncl f U c y
      have hback := congrArg N.coordinate_map hcoords
      simpa only [N.coordinate_map_coordinate_inverse hx.1,
        N.coordinate_map_coordinate_inverse hy.1] using hback
    · intro q
      obtain ⟨t, ht, _⟩ := hroot q
      have hz := hcoord q ⟨ht.1.1.le, ht.1.2.le⟩
      have hx : N.coordinate_map (q, t) ∈ U := by
        refine ⟨N.coordinate_map_mem hz, ?_⟩
        simpa only [N.coordinate_inverse_coordinate_map hz, mem_Ioo] using ht.1
      refine ⟨⟨⟨N.coordinate_map (q, t), hx⟩, ht.2⟩, ?_⟩
      change (N.coordinate_inverse (N.coordinate_map (q, t))).1 = q
      rw [N.coordinate_inverse_coordinate_map hz]
  letI : Nonempty (openLevelSet f U c) :=
    ⟨Classical.choose (hPbij.2 (N.coordinate_inverse N.center).1)⟩
  let F := invFun P
  have hleft : LeftInverse F P := leftInverse_invFun hPbij.1
  have hright : RightInverse F P := rightInverse_invFun hPbij.2
  have hFsmooth : ContMDiff (𝓡 2) (𝓡 2) ∞ F := by
    intro q
    obtain ⟨z, rfl⟩ := hPbij.2 q
    exact Poincare.contMDiffAt_of_local_left_inverse (hPsmooth z)
      (hPderiv z) (Eventually.of_forall hleft)
  let A := openLevelIncl f U c ∘ F
  have hAsmooth : ContMDiff (𝓡 2) (𝓡 3) ∞ A :=
    (contMDiff_openLevelIncl hf U hreg 2 c).comp hFsmooth
  have hAmem (q : UnitTwoSphere) : A q ∈ N.region (-W) W := (F q).1.2
  let h : UnitTwoSphere → ℝ := fun q => (N.coordinate_inverse (A q)).2
  have hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h := by
    intro q
    exact contMDiffAt_snd.comp q
      ((N.coordinate_inverse_smooth.contMDiffAt
        (N.carrier_open.mem_nhds (hAmem q).1)).comp q (hAsmooth q))
  have hgraph (q : UnitTwoSphere) : N.coordinate_map (q, h q) = A q := by
    have hc : (q, h q) = N.coordinate_inverse (A q) :=
      Prod.ext (hright q).symm rfl
    exact (congrArg N.coordinate_map hc).trans
      (N.coordinate_map_coordinate_inverse (hAmem q).1)
  have hgraphfun : (fun q => N.coordinate_map (q, h q)) = A := funext hgraph
  refine ⟨h, hsmooth, fun q => (hAmem q).2, ?_, ?_, ?_⟩
  · intro q
    rw [hgraph]
    exact (F q).2
  · rwa [hgraphfun]
  · rw [hgraphfun]
    ext x
    constructor
    · intro hx
      let z : openLevelSet f U c := ⟨⟨x, hx.1⟩, hx.2⟩
      refine ⟨P z, ?_⟩
      change openLevelIncl f U c (F (P z)) = x
      rw [hleft z]
      rfl
    · rintro ⟨q, rfl⟩
      exact ⟨hAmem q, (F q).2⟩

end PoincareConjecture.EpsilonNeck
