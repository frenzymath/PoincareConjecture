import PoincareConjecture.Proofs.M03.Existence.ConjugatingFlowFamilyNative
import PoincareConjecture.Proofs.M03.Existence.FrameDeTurckDerivativeNative
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.Transform











set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

noncomputable section

universe u

namespace PoincareConjecture.TimeDependentConjugatingFlowNative

variable {n : ℕ} {M : Type u}
  [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "I" => 𝓡 n
local notation "E" => EuclideanSpace ℝ (Fin n)





theorem contMDiffWithinAt_neg_tangentBundleSection
    {X : ℝ → ∀ x : M, TangentSpace I x}
    {u : Set (ℝ × M)} {q₀ : ℝ × M}
    (hX : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (Bundle.TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)) u q₀) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (Bundle.TotalSpace.mk' E q.2 (-(X q.1 q.2)) : TangentBundle I M)) u q₀ := by
  rw [Bundle.contMDiffWithinAt_totalSpace] at hX ⊢
  obtain ⟨hXproj, hXfib⟩ := hX
  refine ⟨hXproj, ?_⟩
  let e := trivializationAt E (TangentSpace I) q₀.2
  have hfib := hXfib.neg
  have hbase : ContinuousWithinAt (fun q : ℝ × M => q.2) u q₀ :=
    continuous_snd.continuousWithinAt
  have hmem : e.baseSet ∈ 𝓝 (q₀.2) :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' q₀.2)
  have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ 𝓝[u] q₀ := hbase hmem
  refine hfib.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hpre] with q hq
    simpa using (e.linear ℝ hq).map_neg (X q.1 q.2)
  · simpa using
      (e.linear ℝ (FiberBundle.mem_baseSet_trivializationAt' q₀.2)).map_neg
        (X q₀.1 q₀.2)

theorem contMDiff_neg_tangentBundleSection
    {X : ℝ → ∀ x : M, TangentSpace I x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (Bundle.TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (Bundle.TotalSpace.mk' E q.2 (-(X q.1 q.2)) : TangentBundle I M)) := by
  intro q
  exact contMDiffWithinAt_neg_tangentBundleSection
    (u := Set.univ) (q₀ := q) (hX q).contMDiffWithinAt

theorem contMDiffWithinAt_neg_intrinsicDeTurckField
    {g : ℝ → RiemannianMetric n M} {background : RiemannianMetric n M}
    (D : ∀ t : ℝ, LeviCivitaData (g t))
    (B : LeviCivitaData background)
    {u : Set (ℝ × M)} {q₀ : ℝ × M}
    (hW : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (Bundle.TotalSpace.mk' E q.2
          (DeTurckNative.intrinsicDeTurckField (D q.1) B q.2) :
            TangentBundle (𝓡 n) M)) u q₀) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (Bundle.TotalSpace.mk' E q.2
          (-(DeTurckNative.intrinsicDeTurckField (D q.1) B q.2)) :
            TangentBundle (𝓡 n) M)) u q₀ :=
  contMDiffWithinAt_neg_tangentBundleSection
    (n := n)
    (X := fun t x => DeTurckNative.intrinsicDeTurckField (D t) B x) hW

theorem contMDiff_neg_intrinsicDeTurckField
    {g : ℝ → RiemannianMetric n M} {background : RiemannianMetric n M}
    (D : ∀ t : ℝ, LeviCivitaData (g t))
    (B : LeviCivitaData background)
    (hW : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (Bundle.TotalSpace.mk' E q.2
          (DeTurckNative.intrinsicDeTurckField (D q.1) B q.2) :
            TangentBundle (𝓡 n) M))) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (Bundle.TotalSpace.mk' E q.2
          (-(DeTurckNative.intrinsicDeTurckField (D q.1) B q.2)) :
            TangentBundle (𝓡 n) M)) :=
  contMDiff_neg_tangentBundleSection
    (n := n)
    (X := fun t x => DeTurckNative.intrinsicDeTurckField (D t) B x) hW

namespace TimeDependentFlowNative

structure SmoothTimeDependentVectorField where
  toFun : (q : M × ℝ) → TangentSpace I q.1
  smooth : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
    (fun q : M × ℝ =>
      (Bundle.TotalSpace.mk' E q.1 (toFun q) : TangentBundle I M))
  suspension : (q : M × ℝ) →
    TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) q
  suspension_eq : ∀ q,
    suspension q =
      ((equivTangentBundleProd I M 𝓘(ℝ, ℝ) ℝ).symm
        ((Bundle.TotalSpace.mk' E q.1 (toFun q) : TangentBundle I M),
          (Bundle.TotalSpace.mk' ℝ q.2 (1 : ℝ) :
            TangentBundle 𝓘(ℝ, ℝ) ℝ))).2
  suspension_smooth : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ))
    (((𝓡 n).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E × ℝ)) ∞
    (fun q : M × ℝ =>
      (Bundle.TotalSpace.mk' (E × ℝ) q (suspension q) :
        TangentBundle ((𝓡 n).prod 𝓘(ℝ, ℝ)) (M × ℝ)))

instance : CoeFun (SmoothTimeDependentVectorField (n := n) (M := M))
    (fun _ => (q : M × ℝ) → TangentSpace I q.1) :=
  ⟨SmoothTimeDependentVectorField.toFun⟩

noncomputable def SmoothTimeDependentVectorField.ofSection
    (X : (q : M × ℝ) → TangentSpace I q.1)
    (hX : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun q : M × ℝ =>
        (Bundle.TotalSpace.mk' E q.1 (X q) : TangentBundle I M))) :
    SmoothTimeDependentVectorField (n := n) (M := M) where
  toFun := X
  smooth := hX
  suspension := fun q =>
    ((equivTangentBundleProd I M 𝓘(ℝ, ℝ) ℝ).symm
      ((Bundle.TotalSpace.mk' E q.1 (X q) : TangentBundle I M),
        (Bundle.TotalSpace.mk' ℝ q.2 (1 : ℝ) :
          TangentBundle 𝓘(ℝ, ℝ) ℝ))).2
  suspension_eq := by intro q; rfl
  suspension_smooth := by
    have hone : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun s : ℝ =>
          (Bundle.TotalSpace.mk' ℝ s (1 : ℝ) : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
      intro s
      apply (contMDiffAt_vectorSpace_iff_contDiffAt
        (V := fun _ : ℝ => ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) s))).2
      exact contDiffAt_const
    have htime : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : M × ℝ =>
          (Bundle.TotalSpace.mk' ℝ q.2 (1 : ℝ) :
            TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
      exact hone.comp contMDiff_snd
    have hpair : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ))
        (((𝓡 n).prod 𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ))) ∞
        (fun q : M × ℝ =>
          ((Bundle.TotalSpace.mk' E q.1 (X q) : TangentBundle I M),
            (Bundle.TotalSpace.mk' ℝ q.2 (1 : ℝ) :
              TangentBundle 𝓘(ℝ, ℝ) ℝ))) := by
      exact hX.prodMk htime
    have hsymm : ContMDiff
        (((𝓡 n).prod 𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)))
        (((𝓡 n).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E × ℝ)) ∞
        ((equivTangentBundleProd I M 𝓘(ℝ, ℝ) ℝ).symm) :=
      contMDiff_equivTangentBundleProd_symm
    exact hsymm.comp hpair

end TimeDependentFlowNative

namespace TimeDependentFlowNative

variable [T2Space M]





structure GlobalTimeDependentFlow
    (V : SmoothTimeDependentVectorField (n := n) (M := M)) where
  Φ : (M × ℝ) → ℝ → (M × ℝ)
  apply_zero : ∀ z : M × ℝ, Φ z 0 = z
  integral_curve : ∀ z : M × ℝ,
    IsMIntegralCurve (Φ z) V.suspension
  time_coord : ∀ (z : M × ℝ) (s : ℝ),
    (Φ z s).2 = z.2 + s
  joint_smooth : ContMDiff
      (((𝓡 n).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
      ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
      (fun z : (M × ℝ) × ℝ => Φ z.1 z.2)

namespace GlobalTimeDependentFlow

variable {V : SmoothTimeDependentVectorField (n := n) (M := M)}

def spatialFlow (G : GlobalTimeDependentFlow V) (t₀ : ℝ) : M → ℝ → M :=
  fun p s => (G.Φ (p, t₀) s).1

theorem trajectory_add (G : GlobalTimeDependentFlow V) (z : M × ℝ)
    (s u : ℝ) :
    G.Φ (G.Φ z s) u = G.Φ z (s + u) := by
  have hV : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ))
      (((𝓡 n).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E × ℝ)) 1
      (fun q : M × ℝ =>
        (Bundle.TotalSpace.mk' (E × ℝ) q (V.suspension q) :
          TangentBundle ((𝓡 n).prod 𝓘(ℝ, ℝ)) (M × ℝ))) :=
    V.suspension_smooth.of_le (by norm_num)
  have hcurve : IsMIntegralCurve (G.Φ z) V.suspension :=
    G.integral_curve z
  have hcurve' : IsMIntegralCurve (G.Φ (G.Φ z s)) V.suspension :=
    G.integral_curve (G.Φ z s)
  have hshift : IsMIntegralCurve ((G.Φ z) ∘ (· + s)) V.suspension :=
    hcurve.comp_add s
  have hzero : ((G.Φ z) ∘ (· + s)) 0 = (G.Φ (G.Φ z s)) 0 := by
    simp [Function.comp_apply, G.apply_zero]
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
    (t₀ := (0 : ℝ)) hV hshift hcurve' hzero
  simpa [Function.comp_apply, add_comm] using (congrFun heq u).symm

theorem trajectory_eq_spatialFlow_prod_time
    (G : GlobalTimeDependentFlow V) (t₀ : ℝ) (p : M) (s : ℝ) :
    G.Φ (p, t₀) s = (G.spatialFlow t₀ p s, t₀ + s) := by
  apply Prod.ext
  · rfl
  · exact G.time_coord (p, t₀) s

theorem spatialFlow_comp
    (G : GlobalTimeDependentFlow V) (t₀ : ℝ) (p : M) (s u : ℝ) :
    G.spatialFlow (t₀ + s) (G.spatialFlow t₀ p s) u =
      G.spatialFlow t₀ p (s + u) := by
  have h := G.trajectory_add (p, t₀) s u
  rw [G.trajectory_eq_spatialFlow_prod_time t₀ p s] at h
  simpa [spatialFlow] using congrArg Prod.fst h

@[simp] theorem spatialFlow_zero
    (G : GlobalTimeDependentFlow V) (t₀ : ℝ) (p : M) :
    G.spatialFlow t₀ p 0 = p := by
  change (G.Φ (p, t₀) 0).1 = p
  rw [G.apply_zero]

theorem spatialFlow_comp_inverse_left
    (G : GlobalTimeDependentFlow V) (t₀ : ℝ) (p : M) (s : ℝ) :
    G.spatialFlow (t₀ + s) (G.spatialFlow t₀ p s) (-s) = p := by
  rw [G.spatialFlow_comp t₀ p s (-s)]
  simp

theorem spatialFlow_comp_inverse_right
    (G : GlobalTimeDependentFlow V) (t₀ : ℝ) (p : M) (s : ℝ) :
    G.spatialFlow t₀ (G.spatialFlow (t₀ + s) p (-s)) s = p := by
  have h := G.spatialFlow_comp_inverse_left (t₀ + s) p (-s)
  simpa [add_assoc, add_comm, add_left_comm] using h

theorem spatialFlow_bijective
    (G : GlobalTimeDependentFlow V) (t₀ s : ℝ) :
    Function.Bijective (fun p : M => G.spatialFlow t₀ p s) := by
  constructor
  · intro p q hpq
    calc
      p = G.spatialFlow (t₀ + s)
          (G.spatialFlow t₀ p s) (-s) :=
        (G.spatialFlow_comp_inverse_left t₀ p s).symm
      _ = G.spatialFlow (t₀ + s)
          (G.spatialFlow t₀ q s) (-s) :=
        congrArg (fun r : M => G.spatialFlow (t₀ + s) r (-s)) hpq
      _ = q := G.spatialFlow_comp_inverse_left t₀ q s
  · intro q
    refine ⟨G.spatialFlow (t₀ + s) q (-s), ?_⟩
    exact G.spatialFlow_comp_inverse_right t₀ q s

theorem contMDiff_spatialFlow_fixed
    (G : GlobalTimeDependentFlow V) (t₀ s : ℝ) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (fun p : M => G.spatialFlow t₀ p s) := by
  let A : M → (M × ℝ) × ℝ := fun p => ((p, t₀), s)
  have hA : ContMDiff (𝓡 n)
      (((𝓡 n).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) ∞ A := by
    exact (contMDiff_id.prodMk contMDiff_const).prodMk contMDiff_const
  have hcomp := G.joint_smooth.comp hA
  simpa [A, spatialFlow] using hcomp.fst

theorem spatialFlow_hasMFDerivAt
    (G : GlobalTimeDependentFlow V) (x : M) (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n)
      (fun s : ℝ => G.spatialFlow 0 x s) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (V (G.spatialFlow 0 x t, t))) := by
  have hcurve := G.integral_curve (x, 0)
  have hproj := (hasMFDerivAt_fst (G.Φ (x, 0) t)).comp t (hcurve t)
  change HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n)
    (Prod.fst ∘ (G.Φ (x, 0))) t _
  have hD : (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (V.toFun (G.spatialFlow 0 x t, t))) =
      (ContinuousLinearMap.fst ℝ (TangentSpace (𝓡 n) (G.Φ (x, 0) t).1)
        (TangentSpace 𝓘(ℝ, ℝ) (G.Φ (x, 0) t).2)) ∘SL
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (V.suspension (G.Φ (x, 0) t))) := by
    apply ContinuousLinearMap.ext
    intro r
    change (r : ℝ) • V.toFun (G.spatialFlow 0 x t, t) =
      (ContinuousLinearMap.fst ℝ _ _)
        (r • V.suspension (G.Φ (x, 0) t))
    rw [V.suspension_eq]
    rw [equivTangentBundleProd_symm_apply_snd]
    change r • V.toFun (G.spatialFlow 0 x t, t) =
      (r • (V.toFun (G.Φ (x, 0) t), (1 : ℝ))).1
    rw [Prod.smul_fst]
    change r • V.toFun ((G.Φ (x, 0) t).1, t) =
      r • V.toFun ((G.Φ (x, 0) t).1, (G.Φ (x, 0) t).2)
    rw [show (G.Φ (x, 0) t).2 = t by simpa using G.time_coord (x, 0) t]
  rw [hD]
  exact hproj

def forwardMap (G : GlobalTimeDependentFlow V) : ℝ → M → M :=
  fun t x => G.spatialFlow 0 x t

def reverseMap (G : GlobalTimeDependentFlow V) : ℝ → M → M :=
  fun t x => G.spatialFlow t x (-t)

theorem contMDiff_forwardMap (G : GlobalTimeDependentFlow V) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × M => G.forwardMap p.1 p.2) := by
  let A : ℝ × M → (M × ℝ) × ℝ := fun p => ((p.2, 0), p.1)
  have hA : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n))
      (((𝓡 n).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) ∞ A := by
    exact (contMDiff_snd.prodMk contMDiff_const).prodMk contMDiff_fst
  have hcomp := G.joint_smooth.comp hA
  simpa [A, forwardMap, spatialFlow] using hcomp.fst

theorem contMDiff_reverseMap (G : GlobalTimeDependentFlow V) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      (fun p : ℝ × M => G.reverseMap p.1 p.2) := by
  let hneg : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞
      (fun t : ℝ => -t) := contDiff_neg.contMDiff
  let A : ℝ × M → (M × ℝ) × ℝ := fun p => ((p.2, p.1), -p.1)
  have hA : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n))
      (((𝓡 n).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)) ∞ A := by
    exact (contMDiff_snd.prodMk contMDiff_fst).prodMk
      (hneg.comp contMDiff_fst)
  have hcomp := G.joint_smooth.comp hA
  simpa [A, reverseMap, spatialFlow] using hcomp.fst

theorem reverseMap_forwardMap (G : GlobalTimeDependentFlow V) (t : ℝ) (x : M) :
    G.reverseMap t (G.forwardMap t x) = x := by
  change G.spatialFlow t (G.spatialFlow 0 x t) (-t) = x
  simpa using G.spatialFlow_comp_inverse_left 0 x t

theorem forwardMap_reverseMap (G : GlobalTimeDependentFlow V) (t : ℝ) (x : M) :
    G.forwardMap t (G.reverseMap t x) = x := by
  change G.spatialFlow 0 (G.spatialFlow t x (-t)) t = x
  simpa using G.spatialFlow_comp_inverse_right 0 x t

noncomputable def diffeomorphFamily
    (G : GlobalTimeDependentFlow V) : ℝ → Diffeomorph (𝓡 n) (𝓡 n) M M ∞ :=
  PoincareConjecture.ConjugatingFlowNative.diffeomorphFamily
    G.contMDiff_forwardMap G.contMDiff_reverseMap
    (fun t x => G.reverseMap_forwardMap t x)
    (fun t x => G.forwardMap_reverseMap t x)

@[simp] theorem diffeomorphFamily_apply
    (G : GlobalTimeDependentFlow V) (t : ℝ) (x : M) :
    G.diffeomorphFamily t x = G.forwardMap t x := rfl

@[simp] theorem diffeomorphFamily_symm_apply
    (G : GlobalTimeDependentFlow V) (t : ℝ) (x : M) :
    (G.diffeomorphFamily t).symm x = G.reverseMap t x := rfl

theorem diffeomorphFamily_zero
    (G : GlobalTimeDependentFlow V) :
    G.diffeomorphFamily 0 = Diffeomorph.refl (𝓡 n) M ∞ := by
  apply Diffeomorph.ext
  intro x
  change G.spatialFlow 0 x 0 = x
  simp

theorem diffeomorphFamily_hasMFDerivAt
    (G : GlobalTimeDependentFlow V) (t : ℝ) (x : M) :
    HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n)
      (fun s : ℝ => G.diffeomorphFamily s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (V (G.diffeomorphFamily t x, t))) := by
  change HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n)
    (fun s : ℝ => G.forwardMap s x) t _
  change HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 n)
    (fun s : ℝ => G.spatialFlow 0 x s) t _
  exact G.spatialFlow_hasMFDerivAt x t

noncomputable def spatialDiffeomorph
    (G : GlobalTimeDependentFlow V) (t₀ s : ℝ) :
    Diffeomorph (𝓡 n) (𝓡 n) M M ∞ :=
  { toEquiv :=
      { toFun := fun p : M => G.spatialFlow t₀ p s
        invFun := fun p : M => G.spatialFlow (t₀ + s) p (-s)
        left_inv := fun p => G.spatialFlow_comp_inverse_left t₀ p s
        right_inv := fun p => G.spatialFlow_comp_inverse_right t₀ p s }
    contMDiff_toFun := G.contMDiff_spatialFlow_fixed t₀ s
    contMDiff_invFun := by
      simpa using G.contMDiff_spatialFlow_fixed (t₀ + s) (-s) }

@[simp] theorem spatialDiffeomorph_apply
    (G : GlobalTimeDependentFlow V) (t₀ s : ℝ) (p : M) :
    G.spatialDiffeomorph t₀ s p = G.spatialFlow t₀ p s := rfl

@[simp] theorem spatialDiffeomorph_symm_apply
    (G : GlobalTimeDependentFlow V) (t₀ s : ℝ) (p : M) :
    (G.spatialDiffeomorph t₀ s).symm p =
      G.spatialFlow (t₀ + s) p (-s) := rfl

end GlobalTimeDependentFlow

end TimeDependentFlowNative

variable {Φ Ψ : ℝ → M → M}



noncomputable def family
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Ψ p.1 p.2))
    (hΨΦ : ∀ (t : ℝ) (x : M), Ψ t (Φ t x) = x)
    (hΦΨ : ∀ (t : ℝ) (x : M), Φ t (Ψ t x) = x) :
    ℝ → Diffeomorph I I M M ∞ :=
  PoincareConjecture.ConjugatingFlowNative.diffeomorphFamily hΦ hΨ hΨΦ hΦΨ

@[simp] theorem family_apply
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Ψ p.1 p.2))
    (hΨΦ : ∀ (t : ℝ) (x : M), Ψ t (Φ t x) = x)
    (hΦΨ : ∀ (t : ℝ) (x : M), Φ t (Ψ t x) = x)
    (t : ℝ) (x : M) :
    family hΦ hΨ hΨΦ hΦΨ t x = Φ t x := rfl

@[simp] theorem family_symm_apply
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Ψ p.1 p.2))
    (hΨΦ : ∀ (t : ℝ) (x : M), Ψ t (Φ t x) = x)
    (hΦΨ : ∀ (t : ℝ) (x : M), Φ t (Ψ t x) = x)
    (t : ℝ) (x : M) :
    (family hΦ hΨ hΨΦ hΦΨ t).symm x = Ψ t x := rfl

theorem family_zero
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Ψ p.1 p.2))
    (hΨΦ : ∀ (t : ℝ) (x : M), Ψ t (Φ t x) = x)
    (hΦΨ : ∀ (t : ℝ) (x : M), Φ t (Ψ t x) = x)
    (h0 : ∀ x, Φ 0 x = x) :
    family hΦ hΨ hΨΦ hΦΨ 0 = Diffeomorph.refl I M ∞ := by
  exact PoincareConjecture.ConjugatingFlowNative.diffeomorphFamily_zero
    hΦ hΨ hΨΦ hΦΨ h0



theorem family_hasMFDerivAt_negW
    (W : (t : ℝ) → (x : M) → TangentSpace I x)
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Ψ p.1 p.2))
    (hΨΦ : ∀ (t : ℝ) (x : M), Ψ t (Φ t x) = x)
    (hΦΨ : ∀ (t : ℝ) (x : M), Φ t (Ψ t x) = x)
    (hgen : ∀ (t : ℝ) (x : M),
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (- W t (Φ t x))))
    (t : ℝ) (x : M) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I
      (fun s : ℝ => family hΦ hΨ hΨΦ hΦΨ s x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (- W t (family hΦ hΨ hΨΦ hΦΨ t x))) := by
  change HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) t
    ((1 : ℝ →L[ℝ] ℝ).smulRight (- W t (Φ t x)))
  exact hgen t x

theorem family_hasMFDerivWithinAt_negW
    (W : (t : ℝ) → (x : M) → TangentSpace I x)
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Φ p.1 p.2))
    (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞
      (fun p : ℝ × M => Ψ p.1 p.2))
    (hΨΦ : ∀ (t : ℝ) (x : M), Ψ t (Φ t x) = x)
    (hΦΨ : ∀ (t : ℝ) (x : M), Φ t (Ψ t x) = x)
    {J : Set ℝ} {t : ℝ} {x : M}
    (hgen : HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      (fun s : ℝ => Φ s x) J t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (- W t (Φ t x)))) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
      (fun s : ℝ => family hΦ hΨ hΨΦ hΦΨ s x) J t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (- W t (family hΦ hΨ hΨΦ hΦΨ t x))) := by
  change HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) J t
    ((1 : ℝ →L[ℝ] ℝ).smulRight (- W t (Φ t x)))
  exact hgen

end PoincareConjecture.TimeDependentConjugatingFlowNative

end
