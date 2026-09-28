import PoincareConjecture.Proofs.M09.AdaptedFieldOn
import PoincareConjecture.Proofs.M09.OpenODEUniqueness
import PoincareConjecture.Proofs.M09.CurvePhase








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

theorem adaptedField_eventuallyEq {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (P Q : ∀ t, TangentSpace (𝓡 n) (γ t))
    (U : Set ℝ) (hU : IsOpen U) (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (hP : IsAdaptedFieldOn F T γ P U) (hQ : IsAdaptedFieldOn F T γ Q U)
    (s0 : ℝ) (hs0 : s0 ∈ U) (heq : P s0 = Q s0) :
    ∀ᶠ t in 𝓝 s0, P t = Q t := by
  let p := γ s0
  let e := chartAt E p
  let D := U ∩ γ ⁻¹' e.source
  have hD : IsOpen D := hγ.continuousOn.isOpen_inter_preimage hU e.open_source
  have hsD : s0 ∈ D := ⟨hs0, mem_chart_source E p⟩
  let y : ℝ → E := fun t ↦ e (γ t)
  let v : ℝ → E := fun t ↦ mfderiv (𝓡 n) (𝓡 n) e (γ t) (P t)
  let w : ℝ → E := fun t ↦ mfderiv (𝓡 n) (𝓡 n) e (γ t) (Q t)
  have hy : ContDiffOn ℝ ∞ y D :=
    (contMDiffOn_chart.comp (hγ.mono Set.inter_subset_left) (fun _ ht ↦ ht.2)).contDiffOn
  have hdy : ContDiffOn ℝ ∞ (deriv y) D := hy.deriv_of_isOpen hD (by simp)
  let S := Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ e.target
  have hS : IsOpen S := isOpen_Ioo.prod e.open_target
  have hL := coordinateTransportOperator_contDiffOn (squareChartMetric F T p) S hS
    (squareChartMetric_smooth F T b hb hwindow p)
    (fun z hz a ha ↦ squareChartMetric_pos F T p z hz.2 a ha)
  let A : ℝ → E →L[ℝ] E := fun t ↦
    coordinateTransportOperator (squareChartMetric F T p) (t, y t) (deriv y t)
  have hparam : ContDiffOn ℝ ∞ (fun t : ℝ ↦ ((t, y t), deriv y t)) D :=
    (contDiffOn_id.prodMk hy).prodMk hdy
  have hA := hL.comp (f := fun t : ℝ ↦ ((t, y t), deriv y t)) hparam
    (fun t ht ↦ ⟨⟨htime ht.1, e.map_source ht.2⟩, Set.mem_univ _⟩)
  let B : ℝ × E → E := fun z ↦ A z.1 z.2
  have hB : ContDiffOn ℝ 1 B (D ×ˢ Set.univ) :=
    ((hA.comp contDiffOn_fst (fun _ hz ↦ hz.1)).clm_apply contDiffOn_snd).of_le (by simp)
  have hv : ∀ t ∈ D, (t, v t) ∈ D ×ˢ Set.univ ∧ HasDerivAt v (B (t, v t)) t := by
    intro t ht
    exact ⟨⟨ht, Set.mem_univ _⟩, hP.equation t ht.1 p ht.2⟩
  have hw : ∀ t ∈ D, (t, w t) ∈ D ×ˢ Set.univ ∧ HasDerivAt w (B (t, w t)) t := by
    intro t ht
    exact ⟨⟨ht, Set.mem_univ _⟩, hQ.equation t ht.1 p ht.2⟩
  have h0 : v s0 = w s0 := congrArg (mfderiv (𝓡 n) (𝓡 n) e (γ s0)) heq
  have hsame := openODE_eventuallyEq (D ×ˢ Set.univ) (hD.prod isOpen_univ) B hB
    v w s0 (hv s0 hsD).1 h0
    (Filter.Eventually.mono (hD.mem_nhds hsD) (fun t ht ↦ hv t ht))
    (Filter.Eventually.mono (hD.mem_nhds hsD) (fun t ht ↦ hw t ht))
  filter_upwards [hD.mem_nhds hsD, hsame] with t ht htw
  calc
    P t = chartVectorField p (v t) (γ t) :=
      (chartVectorField_differential p (γ t) (P t) ht.2).symm
    _ = chartVectorField p (w t) (γ t) := by rw [htw]
    _ = Q t := chartVectorField_differential p (γ t) (Q t) ht.2

theorem adaptedField_eqOn {J : Set ℝ} [T2Space M] (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (γ : ℝ → M) (P Q : ∀ t, TangentSpace (𝓡 n) (γ t))
    (U : Set ℝ) (hU : IsOpen U) (hconn : IsPreconnected U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (hP : IsAdaptedFieldOn F T γ P U) (hQ : IsAdaptedFieldOn F T γ Q U)
    (s0 : ℝ) (hs0 : s0 ∈ U) (heq : P s0 = Q s0) : ∀ t ∈ U, P t = Q t := by
  letI : T2Space (TangentBundle (𝓡 n) M) := tangentBundle_t2Space
  letI : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  let A : Set U := {t | (⟨γ t, P t⟩ : TangentBundle (𝓡 n) M) = ⟨γ t, Q t⟩}
  have hclosed : IsClosed A := isClosed_eq hP.smooth.continuousOn.domRestrict
    hQ.smooth.continuousOn.domRestrict
  have hopen : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have ht' : P t = Q t := congrArg (fun z : TangentBundle (𝓡 n) M ↦ (z.2 : E)) ht
    have hlocal := adaptedField_eventuallyEq F T b hb hwindow γ P Q U hU htime
      hγ hP hQ t t.property ht'
    have hnear : ∀ᶠ r : U in 𝓝 t, P r = Q r :=
      continuousAt_subtype_val.tendsto.eventually hlocal
    filter_upwards [hnear] with r hr
    change (⟨γ r, P r⟩ : TangentBundle (𝓡 n) M) = ⟨γ r, Q r⟩
    rw [hr]
  have h0 : (⟨s0, hs0⟩ : U) ∈ A := by
    change (⟨γ s0, P s0⟩ : TangentBundle (𝓡 n) M) = ⟨γ s0, Q s0⟩
    rw [heq]
  have hAll : A = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨s0, hs0⟩, h0⟩
  intro t ht
  have hm : (⟨t, ht⟩ : U) ∈ A := by rw [hAll]; trivial
  exact congrArg (fun z : TangentBundle (𝓡 n) M ↦ (z.2 : E)) hm

end PoincareConjecture.Proofs.M09
