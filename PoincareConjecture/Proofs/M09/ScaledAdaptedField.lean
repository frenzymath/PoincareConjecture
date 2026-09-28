import PoincareConjecture.Proofs.M09.AdaptedFieldOn
import PoincareConjecture.Proofs.M09.RicciContractions
import Mathlib.Analysis.Calculus.Deriv.Mul








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem field_smul_smooth (γ : ℝ → M) (P : ∀ t, TangentSpace (𝓡 n) (γ t))
    (f : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U) (hf : ContDiffOn ℝ ∞ f U)
    (hP : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun t ↦ (⟨γ t, P t⟩ : TangentBundle (𝓡 n) M)) U) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun t ↦ (⟨γ t, f t • P t⟩ : TangentBundle (𝓡 n) M)) U := by
  intro s hs
  let p := γ s
  let V := U ∩ γ ⁻¹' (chartAt E p).source
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU (chartAt E p).open_source
  have hsV : s ∈ V := ⟨hs, mem_chart_source E p⟩
  have hq : ∀ t ∈ V, γ t ∈ (chartAt E p).source := fun _ ht ↦ ht.2
  let v : ℝ → E := fun t ↦ mfderiv (𝓡 n) (𝓡 n) (chartAt E p) (γ t) (P t)
  have hv := field_chart_coordinates_smooth p γ P V (hP.mono Set.inter_subset_left) hq
  have hfv := (hf.mono Set.inter_subset_left).smul hv
  have hlocal : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun t ↦ (⟨γ t, chartVectorField p (f t • v t) (γ t)⟩ : TangentBundle (𝓡 n) M)) V :=
    (chartVectorField_param_smooth p (fun t ↦ f t • v t) V hfv).comp
      (contMDiffOn_id.prodMk (hγ.mono Set.inter_subset_left)) (fun t ht ↦ ⟨ht, ht.2⟩)
  apply ((hlocal.contMDiffAt (hV.mem_nhds hsV)).congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hV.mem_nhds hsV] with t ht
  have hrep := chartVectorField_differential p (γ t) (P t) ht.2
  change (⟨γ t, f t • P t⟩ : TangentBundle (𝓡 n) M) =
    ⟨γ t, (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) (γ t)).inverse (f t • v t)⟩
  rw [map_smul]
  change (⟨γ t, f t • P t⟩ : TangentBundle (𝓡 n) M) =
    ⟨γ t, f t • chartVectorField p (v t) (γ t)⟩
  rw [hrep]

set_option backward.isDefEq.respectTransparency false in
theorem pullbackCovariantDerivative_smul {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (P : ∀ t, TangentSpace (𝓡 n) (γ t)) (f : ℝ → ℝ)
    (K U : Set ℝ) (hU : IsOpen U)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U) (hf : ContDiffOn ℝ ∞ f U)
    (hP : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun t ↦ (⟨γ t, P t⟩ : TangentBundle (𝓡 n) M)) U)
    (HP : ParametricAlongCurveExtensionOn (n := n) K γ P)
    (HY : ParametricAlongCurveExtensionOn (n := n) K γ (fun t ↦ f t • P t))
    (s : ℝ) (hs : s ∈ K) (hsU : s ∈ U) (hKd : UniqueDiffWithinAt ℝ K s)
    (htime : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) :
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ (fun t ↦ f t • P t) K HY s =
      deriv f s • P s + f s • pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ P K HP s := by
  let p := γ s
  let e := chartAt E p
  let V := U ∩ γ ⁻¹' e.source
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU e.open_source
  have hsV : s ∈ V := ⟨hsU, mem_chart_source E p⟩
  have hq : ∀ t ∈ V, γ t ∈ e.source := fun _ ht ↦ ht.2
  let v : ℝ → E := fun t ↦ mfderiv (𝓡 n) (𝓡 n) e (γ t) (P t)
  have hv := field_chart_coordinates_smooth p γ P V (hP.mono Set.inter_subset_left) hq
  have hvrep : ∀ t ∈ V, chartVectorField p (v t) (γ t) = P t :=
    fun t ht ↦ chartVectorField_differential p (γ t) (P t) ht.2
  have hfv := (hf.mono Set.inter_subset_left).smul hv
  have hfvrep : ∀ t ∈ K ∩ V, chartVectorField p (f t • v t) (γ t) = f t • P t := by
    intro t ht
    change (mfderiv (𝓡 n) (𝓡 n) e (γ t)).inverse (f t • v t) = _
    rw [map_smul]
    exact congrArg (fun x : TangentSpace (𝓡 n) (γ t) ↦ f t • x) (hvrep t ht.2)
  have hpullP := pullbackCovariantDerivative_eq_chart F T b hb hwindow p γ P K V HP
    hV (hγ.mono Set.inter_subset_left) hq v hv (fun t ht ↦ hvrep t ht.2)
    s hs hsV hKd htime
  have hpullY := pullbackCovariantDerivative_eq_chart F T b hb hwindow p γ
    (fun t ↦ f t • P t) K V HY hV (hγ.mono Set.inter_subset_left) hq
    (fun t ↦ f t • v t) hfv hfvrep s hs hsV hKd htime
  have hfd := ((hf.contDiffAt (hU.mem_nhds hsU)).differentiableAt (by simp)).hasDerivAt
  have hvd := ((hv.contDiffAt (hV.mem_nhds hsV)).differentiableAt (by simp)).hasDerivAt
  have hd : deriv (fun t ↦ f t • v t) s = deriv f s • v s + f s • deriv v s :=
    (hfd.smul hvd).deriv.trans (add_comm _ _)
  rw [hpullY, hpullP, hd, coordinateConnection_smul_right]
  change (mfderiv (𝓡 n) (𝓡 n) e (γ s)).inverse _ =
    deriv f s • P s + f s • (mfderiv (𝓡 n) (𝓡 n) e (γ s)).inverse _
  simp only [map_add, map_smul, smul_add]
  rw [show (mfderiv (𝓡 n) (𝓡 n) e (γ s)).inverse (v s) = P s from hvrep s hsV]
  abel

set_option backward.isDefEq.respectTransparency false in
theorem IsAdaptedFieldOn.pullback_eq_ricciOperator {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (P : ∀ t, TangentSpace (𝓡 n) (γ t)) (K U : Set ℝ)
    (hU : IsOpen U) (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (hP : IsAdaptedFieldOn F T γ P U) (H : ParametricAlongCurveExtensionOn (n := n) K γ P)
    (s : ℝ) (hs : s ∈ K) (hsU : s ∈ U) (hKd : UniqueDiffWithinAt ℝ K s)
    (htime : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) :
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ P K H s =
      (-(2 * s)) • ricciOperator hM04 (F.connection (T - s ^ 2)) (γ s) (P s) := by
  let A := pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ P K H s
  let B := (-(2 * s)) • ricciOperator hM04 (F.connection (T - s ^ 2)) (γ s) (P s)
  have hpair (w : TangentSpace (𝓡 n) (γ s)) :
      (F.metric (T - s ^ 2)).inner (γ s) (A - B) w = 0 := by
    have h := pullback_adapted_of_localAdaptedEquation F T b hb hwindow γ P K U H
      hU hγ hP.smooth s hs hsU hKd htime (hP.equation s hsU) w
    simp only [A, B, map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul,
      ricciOperator_pairing]
    exact sub_eq_zero.mpr h
  apply sub_eq_zero.mp
  by_contra hne
  exact (ne_of_gt ((F.metric (T - s ^ 2)).pos (γ s) (A - B) hne)) (hpair (A - B))

theorem IsAdaptedFieldOn.scaled_pullback {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (P : ∀ t, TangentSpace (𝓡 n) (γ t)) (f : ℝ → ℝ)
    (K U : Set ℝ) (hU : IsOpen U)
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U) (hf : ContDiffOn ℝ ∞ f U)
    (hP : IsAdaptedFieldOn F T γ P U)
    (HP : ParametricAlongCurveExtensionOn (n := n) K γ P)
    (HY : ParametricAlongCurveExtensionOn (n := n) K γ (fun t ↦ f t • P t))
    (s : ℝ) (hs : s ∈ K) (hsU : s ∈ U) (hKd : UniqueDiffWithinAt ℝ K s)
    (htime : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) :
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) γ (fun t ↦ f t • P t) K HY s =
      deriv f s • P s - (2 * s * f s) •
        ricciOperator hM04 (F.connection (T - s ^ 2)) (γ s) (P s) := by
  rw [pullbackCovariantDerivative_smul F T b hb hwindow γ P f K U hU hγ hf hP.smooth
    HP HY s hs hsU hKd htime,
    IsAdaptedFieldOn.pullback_eq_ricciOperator F hM04 T b hb hwindow γ P K U hU hγ
      hP HP s hs hsU hKd htime, smul_smul]
  rw [show f s * -(2 * s) = -(2 * s * f s) by ring, neg_smul, ← sub_eq_add_neg]

end PoincareConjecture.Proofs.M09
