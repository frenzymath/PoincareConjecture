import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.Field
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Pullback.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.LGeometry.Surface








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Frame

open Geometry

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_orthonormalBasis_eq (g : RiemannianMetric n M) (x : M)
    (P : Fin n → TangentSpace (𝓡 n) x)
    (hP : ∀ i j, g.inner x (P i) (P j) = if i = j then 1 else 0) :
    ∃ e : letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      OrthonormalBasis (Fin n) ℝ (TangentSpace (𝓡 n) x), ∀ i, e i = P i := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n)))
  have hon : Orthonormal ℝ P := orthonormal_iff_ite.mpr hP
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace (𝓡 n) x) := by
    exact (Fintype.card_fin n).trans (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)).symm
  let e := OrthonormalBasis.mk hon
    (hon.linearIndependent.span_eq_top_of_card_eq_finrank' hcard).ge
  exact ⟨e, fun i ↦ congrFun (OrthonormalBasis.coe_mk hon _) i⟩

theorem parametricExtension_field_contMDiffOn {U : Set ℝ} {α : ℝ → M}
    {P : ∀ s, TangentSpace (𝓡 n) (α s)}
    (E : ParametricAlongCurveExtensionOn U α P)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (P s)) U := by
  have h := E.smooth.comp (contMDiffOn_id.prodMk hα) (fun s hs ↦ E.graph_mem s hs)
  apply h.congr
  intro s hs
  dsimp only [Function.comp_def, id_eq]
  rw [E.agrees s hs]

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Frame

open Geometry

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem pullback_adapted_surface {J C U : Set ℝ} (F : RicciFlow 2 M J)
    (T : ℝ) (α : ℝ → M) (P : ∀ s, TangentSpace (𝓡 2) (α s))
    (E : ParametricAlongCurveExtensionOn C α P) (hU : IsOpen U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) ∞ α U)
    (hP : IsAdaptedFieldOn F T α P U) {s : ℝ} (hs : s ∈ C) (hsU : s ∈ U)
    (hC : UniqueDiffWithinAt ℝ C s)
    (htime : s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J)) :
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α P C E s =
      (-(s * (F.connection (T - s ^ 2)).scalarCurvature (α s))) • P s := by
  let g := F.metric (T - s ^ 2)
  let Q := pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α P C E s
  let a := -(s * (F.connection (T - s ^ 2)).scalarCurvature (α s))
  have hpair (Z : TangentSpace (𝓡 2) (α s)) : g.inner (α s) Q Z = g.inner (α s) (a • P s) Z := by
    have h := pullback_adapted_of_localAdaptedEquation F T α P E hU hα hP.smooth
      hs hsU hC htime (hP.equation s hsU) Z
    rw [(F.connection (T - s ^ 2)).ricci_eq_half_scalarCurvature_mul_inner] at h
    dsimp only [g, Q, a]
    rw [h]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hz : g.inner (α s) (Q - a • P s) (Q - a • P s) = 0 := by
    rw [(g.inner (α s)).map_sub, sub_apply, hpair, sub_self]
  have heq : Q - a • P s = 0 := by
    by_contra hn
    exact (ne_of_gt (g.pos (α s) _ hn)) hz
  exact sub_eq_zero.mp heq

theorem pullback_scaled_adapted_surface {J C U : Set ℝ} (F : RicciFlow 2 M J)
    (T : ℝ) (α : ℝ → M) (P : ∀ s, TangentSpace (𝓡 2) (α s))
    (E : ParametricAlongCurveExtensionOn C α P) (c : ℝ)
    (H : ParametricAlongCurveExtensionOn C α (fun s ↦ (s / c) • P s))
    (hU : IsOpen U) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) ∞ α U)
    (hP : IsAdaptedFieldOn F T α P U) {s : ℝ} (hs : s ∈ C) (hsU : s ∈ U)
    (hC : UniqueDiffWithinAt ℝ C s)
    (htime : s ∈ interior ((fun r : ℝ ↦ T - r ^ 2) ⁻¹' J)) :
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α
        (fun r ↦ (r / c) • P r) C H s =
      (1 / c - s * (s / c) * (F.connection (T - s ^ 2)).scalarCurvature (α s)) • P s := by
  have hd : deriv (fun r : ℝ ↦ r / c) s = 1 / c := by
    simpa only [id_eq] using ((hasDerivAt_id s).div_const c).deriv
  rw [pullbackCovariantDerivative_smul F (fun r ↦ T - r ^ 2) E
    (fun r ↦ r / c) (contDiff_id.div_const c) H hs hC
    (((hα s hsU).contMDiffAt (hU.mem_nhds hsU)).mdifferentiableAt (by simp)),
    hd,
    pullback_adapted_surface F T α P E hU hα hP hs hsU hC htime,
    smul_smul, ← add_smul]
  congr 1
  ring

end PoincareConjecture.ReducedLengthMinimum.Variation.Frame
